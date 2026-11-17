-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_4
-- name    : RestrictedDec.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:38:00.907771+00:00
-- url     : https://prove2.me/theorems/7929eb97-8214-4570-9e7a-4b0e6e6da2ef
-- title:
--   Theorem 4 — strict adaptive chains $\mathrm{Sec}^{ad}(\mathcal F_t)\subsetneq\cdots\subsetneq\mathrm{Sec}^{ad}(\mathcal F_0)$ from IND-CCA2
-- statement:
--   Let $M$ be a common message space and assume an efficient IND-CCA2-secure public-key encryption scheme over $M$ exists. Then:
--
--   1. for valid families $\mathcal F\preceq\mathcal G$ over $M$ (oracle simulation, §3.1) with an efficiently found separating witness — messages $m_0,m_1$ that are valid, of equal length and agree under every function of $\mathcal F$ at every security parameter, and an efficiently specified $G^\star\in\mathcal G$ with $G^\star(m_0)\neq G^\star(m_1)$ on infinitely many security parameters — the asymptotic inclusion is strict:
--   $$\mathrm{Sec}^{ad}(\mathcal G)\subsetneq\mathrm{Sec}^{ad}(\mathcal F);$$
--   2. in particular, a fixed finite chain $\mathcal F_0\preceq\mathcal F_1\preceq\cdots\preceq\mathcal F_t$ of valid families with a separating witness at every step satisfies
--   $$\mathrm{Sec}^{ad}(\mathcal F_t)\subsetneq\mathrm{Sec}^{ad}(\mathcal F_{t-1})\subsetneq\cdots\subsetneq\mathrm{Sec}^{ad}(\mathcal F_0).$$
--
--   Strictness means that every efficient scheme over $M$ secure for the stronger class is secure for the weaker one and one efficient scheme is secure for the weaker class but broken by a single uniform attack for the stronger one. Giving the adversary strictly more information through the oracle therefore always yields a strictly harder adaptive security requirement, along hierarchies of any length.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - generalization: classes and adjacent separating witnesses uniformly computable from a binary index i, for any uniformly computable pair of adjacent index sequences (and t = t(λ) interpreted uniformly) → arbitrary valid λ-indexed families F ⪯ G with an efficiently found separating witness; reason: the classes along a pair of uniformly computable index sequences form such λ-indexed families, so the statement specializes to the paper's
--   - reading: the adjacent classes satisfy F_{i−1} ⪯ F_i → hypothesis Simulates M F G (randomized same-point simulation with one negligible error, §3.1); reason: the chain F₀ ⪯ F₁ ⪯ ⋯ ⪯ F_t of §3.3, p.18, which the proof uses for the inclusion
--   - encoding: witness messages valid, equal-length and agreeing under every weaker function at every security parameter; distinguished by an efficiently specified stronger function on infinitely many parameters → SepWitness M F G: one polynomial-time machine outputs (m₀(λ), m₁(λ), d*(λ)); the agreement at every λ, admissibility and separation by d*(λ) on infinitely many λ; reason: §3.3, pp.18–19
--   - reading: the corresponding asymptotic security inclusion is strict (the same condition and indexing convention as Theorem 3) → SecSubsetneq: the inclusion for every efficient scheme over M and one efficient scheme in Sec(F) \ Sec(G), both for an adjacent pair and along a finite chain; reason: asymptotic strictness, §2.3, p.15
--   - encoding: chain indices 0, …, t with adjacent pair (F_{i−1}, F_i) → families Fs 0, …, Fs t with adjacent pairs (Fs i, Fs (i+1)) for i < t; reason: re-indexing; avoids natural-number subtraction
--   - encoding: the common message space; uniform evaluation of each class → hypotheses MsgSpace.Found M and FamilyValidM; reason: standing assumptions of §2.1, pp.12–13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 4, p.21; §3.3, pp.18–19

import Mathlib
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_FamilyValidM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_SecSubsetneq
import Definitions.Def_RestrictedDec_Supplement_Simulates
import Definitions.Def_RestrictedDec_Supplement_SepWitness
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 4** (strict adaptive chains). Let `M` be a common message space and assume an efficient
IND-CCA2-secure public-key encryption scheme over `M` exists.
1. For valid families `𝓕 ⪯ 𝓖` with an efficiently found separating witness (messages valid,
   equal-length and agreeing under every function of `𝓕` at every `λ`, distinguished by an
   efficiently specified function of `𝓖` on infinitely many `λ`), the inclusion is strict:
   `Sec^ad(𝓖) ⊊ Sec^ad(𝓕)`.
2. In particular, a fixed finite chain `𝓕₀ ⪯ 𝓕₁ ⪯ ⋯ ⪯ 𝓕_t` of valid families with a separating
   witness at every step satisfies `Sec^ad(𝓕_t) ⊊ Sec^ad(𝓕_{t−1}) ⊊ ⋯ ⊊ Sec^ad(𝓕₀)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 4, p.21; the
separation condition of §3.3, pp.18–19; asymptotic strictness, §2.3, p.15.

**Formalization Note.** The classes are λ-indexed families (`Family`), which covers the paper's
binary-indexed classes along any uniformly computable pair of adjacent index sequences; the chain
is indexed `0, …, t` and step `i → i + 1` is the paper's `i − 1 → i`. -/
theorem theorem_4 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M)
    (hCCA : ∃ E : PKE, IsSchemeM M E ∧ INDCCA2M M E) :
    (∀ F G : Family, FamilyValidM M F → FamilyValidM M G → Simulates M F G →
      SepWitness M F G → SecSubsetneq .ad M G F) ∧
    (∀ (t : ℕ) (Fs : ℕ → Family), (∀ i ≤ t, FamilyValidM M (Fs i)) →
      (∀ i < t, Simulates M (Fs i) (Fs (i + 1)) ∧ SepWitness M (Fs i) (Fs (i + 1))) →
      ∀ i < t, SecSubsetneq .ad M (Fs (i + 1)) (Fs i)) := by sorry

end Supplement

end RestrictedDec
