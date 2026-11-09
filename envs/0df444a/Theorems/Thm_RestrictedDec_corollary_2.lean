-- Prove2me | Theorems.Thm_RestrictedDec_corollary_2
-- name    : RestrictedDec.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:56:56.77781+00:00
-- url     : https://prove2.me/theorems/1fe12ff4-aa9f-4914-98ba-2a3ad8c301eb
-- title:
--   Corollary 2 — $\mathrm{Sec}^{ad}(q_S)$ and $\mathrm{Sec}^{na}(q_T)$ are incomparable when $S\neq\emptyset$ and $T\not\subseteq S$
-- statement:
--   Assume that an efficient IND-CCA2-secure public-key encryption scheme exists for the message space $\{0,1\}^{n(\lambda)}$, where $n(\lambda)$ is a public polynomially bounded message length. Let $S_\lambda,T_\lambda\subseteq[n(\lambda)]$ be uniformly computable public coordinate sets.
--
--   1. If $S_\lambda\neq\emptyset$ and $T_\lambda\setminus S_\lambda\neq\emptyset$ for all sufficiently large $\lambda$, then the security classes $\mathrm{Sec}^{ad}(q_S)$ and $\mathrm{Sec}^{na}(q_T)$ are incomparable:
--   $$\mathrm{Sec}^{ad}(q_S)\not\subseteq\mathrm{Sec}^{na}(q_T),\qquad \mathrm{Sec}^{na}(q_T)\not\subseteq\mathrm{Sec}^{ad}(q_S).$$
--   That is, there is an efficient scheme over $\{0,1\}^{n(\lambda)}$ in $\mathrm{Sec}^{ad}(q_S)$ but not in $\mathrm{Sec}^{na}(q_T)$, and an efficient scheme over $\{0,1\}^{n(\lambda)}$ in $\mathrm{Sec}^{na}(q_T)$ but not in $\mathrm{Sec}^{ad}(q_S)$.
--   2. In particular, the same holds if $\emptyset\neq S_\lambda\subsetneq T_\lambda$ for all sufficiently large $\lambda$.
--
--   When both the observation and the query timing change, neither requirement implies the other: adaptive access to a coarse observation and pre-challenge access to a finer one are incomparable.
--
--   Differences from the source:
--   - reading: n(λ) polynomially bounded → PolyParam n: polynomially bounded and 1^{n(λ)} computable from 1^λ in polynomial time; reason: p.13 assumes the common message space has efficiently found messages; the constructions need 0ⁿ, e_i, e_j
--   - reading: public-key encryption scheme over {0,1}^{n(λ)} → PKE with PKE.IsScheme n (polynomial-time algorithms, Dec into M_⊥); reason: App. A.1, p.29 and the efficiency of PKE schemes; kept apart from Sec
--   - reading: IND-CCA1 / IND-CCA2 → INDCCA1 = Sec^na(𝓕_id), INDCCA2 = Sec^ad(𝓕_id); reason: §2.2, p.14: the requirements coincide, including ordinary correctness
--   - reading: Sec^ad(q_S) ⊄ Sec^na(q_T) (non-inclusion of security classes) → ∃ P, P.IsScheme n ∧ P ∈ one class ∧ P ∉ the other; reason: p.15: a strict separation is a single uniformly constructible scheme against a single PPT attack
--   - reading: "In particular, this holds for ∅ ≠ S ⊊ T" (no quantifier over λ printed) → (∀ᶠ λ, S λ nonempty ∧ S λ ⊂ T λ) implies the same conclusion; reason: the corollary's own "for all sufficiently large λ" convention; the eventual hypothesis is implied by the for-every-λ reading, so the Lean clause covers both readings
--   - encoding: S_λ, T_λ ⊆ [n(λ)] uniformly computable → UniformSets: S λ ⊆ {1, …, n λ} and its characteristic vector computed from 1^λ in polynomial time; reason: the paper's uniformity convention, §2.3 p.15
--   - reading: every PPT adversary → every uniform reactive machine with a polynomial-time step function and polynomial bounds on coins, state, moves and activations; reason: the paper's adversaries are uniform (p.15 'a single PPT attack', p.28 'a uniform adversary')
--   - encoding: invalid challenge, missing guess, inadmissible query → the run ends with guess 0 (success probability 1/2); inadmissible queries are refused; reason: conventions of the experiment that change no advantage
--   - encoding: messages, keys, ciphertexts, pairs (β, c), positions in [n] → bit strings Str, (β, c) as β :: c, ⊥ as none, positions numbered from 1; reason: Lean convention; same instances
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Corollary 2, p.22

import Mathlib
import Definitions.Def_RestrictedDec_PolyParam
import Definitions.Def_RestrictedDec_UniformSets
import Definitions.Def_RestrictedDec_PKE_IsScheme
import Definitions.Def_RestrictedDec_INDCCA2
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_qCoord
open QAlgorithms.Complexity
open Filter
set_option autoImplicit false

namespace RestrictedDec

/-- **Corollary 2** (crossed incomparability). Assume an efficient IND-CCA2-secure public-key
encryption scheme exists for the message space `{0,1}^{n(λ)}`, where `n(λ)` is a public polynomial
message length. Let `S_λ, T_λ ⊆ [n(λ)]` be uniformly computable public coordinate sets.
1. If `S_λ ≠ ∅` and `T_λ \ S_λ ≠ ∅` for all sufficiently large `λ`, then `Sec^ad(q_S)` and
   `Sec^na(q_T)` are incomparable: some efficient scheme is in `Sec^ad(q_S)` but not in
   `Sec^na(q_T)`, and some efficient scheme is in `Sec^na(q_T)` but not in `Sec^ad(q_S)`.
2. In particular, the same holds if `∅ ≠ S_λ ⊊ T_λ` for all sufficiently large `λ`.
Nguyen–Susilo, *Between CPA and CCA: Security Hierarchies for Restricted Decryption*, STOC 2027
submission (manuscript sha256 6aeac40c…), Corollary 2, p.22. -/
theorem corollary_2 (n : ℕ → ℕ) (hn : PolyParam n) (S T : ℕ → Finset ℕ)
    (hS : UniformSets n S) (hT : UniformSets n T)
    (hCCA : ∃ E : PKE, E.IsScheme n ∧ INDCCA2 n E) :
    ((∀ᶠ lam in atTop, (S lam).Nonempty ∧ (T lam \ S lam).Nonempty) →
      (∃ P : PKE, P.IsScheme n ∧ Sec .ad n (famObs (qCoord S)) P ∧
          ¬ Sec .na n (famObs (qCoord T)) P) ∧
        (∃ P : PKE, P.IsScheme n ∧ Sec .na n (famObs (qCoord T)) P ∧
          ¬ Sec .ad n (famObs (qCoord S)) P)) ∧
    ((∀ᶠ lam in atTop, (S lam).Nonempty ∧ S lam ⊂ T lam) →
      (∃ P : PKE, P.IsScheme n ∧ Sec .ad n (famObs (qCoord S)) P ∧
          ¬ Sec .na n (famObs (qCoord T)) P) ∧
        (∃ P : PKE, P.IsScheme n ∧ Sec .na n (famObs (qCoord T)) P ∧
          ¬ Sec .ad n (famObs (qCoord S)) P)) := by sorry

end RestrictedDec
