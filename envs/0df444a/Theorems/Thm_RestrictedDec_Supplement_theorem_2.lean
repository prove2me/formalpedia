-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_2
-- name    : RestrictedDec.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:36:02.770125+00:00
-- url     : https://prove2.me/theorems/74366596-02aa-4c81-a048-c7ba11eb6a14
-- title:
--   Theorem 2 — $E\in\mathrm{Sec}^{na}(\mathcal F)$ yields $E^\dagger\in\mathrm{Sec}^{na}(\mathcal F)\setminus\mathrm{Sec}^{ad}(\mathcal F)$; timing strictness
-- statement:
--   Let $M$ be a common message space and $\mathcal F$ a valid family of permitted functions over $M$. Suppose $\mathcal F$ contains an efficiently specified function $F^\star$ and uniformly computable valid equal-length messages $u_0,u_1$ with
--   $$F^\star(u_0)\neq F^\star(u_1),$$
--   that is, one polynomial-time machine computes from $1^\lambda$ an admissible description of $F^\star$ and $u_0,u_1\in M_\lambda$, $|u_0|=|u_1|$, with this property, for every $\lambda$. Then:
--
--   1. from every efficient scheme $E\in\mathrm{Sec}^{na}(\mathcal F)$ one obtains an efficient scheme $E^\dagger\in\mathrm{Sec}^{na}(\mathcal F)\setminus\mathrm{Sec}^{ad}(\mathcal F)$;
--   2. in particular, $\mathrm{Sec}^{ad}(\mathcal F)\subseteq\mathrm{Sec}^{na}(\mathcal F)$, and whenever pre-challenge security for $\mathcal F$ is achievable by an efficient scheme, some efficient scheme is pre-challenge secure but not adaptively secure: the inclusion is strict.
--
--   The separation isolates the effect of query timing for one fixed function class: a ciphertext transformation available only after the challenge turns a single permitted query into a distinguisher.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: F* efficiently specified; u₀, u₁ uniformly computable → one polynomial-time machine outputs, for every λ, an admissible description d(λ) and u₀(λ), u₁(λ) ∈ M_λ of equal length with F*_{d(λ)}(u₀) ≠ F*_{d(λ)}(u₁); reason: the uniformity convention of §2.3, p.15
--   - encoding: from any scheme E ∈ Sec^na(F) one can construct a scheme E† → for every efficient E ∈ Sec^na(F) there is an efficient E† ∈ Sec^na(F) with E† ∉ Sec^ad(F); reason: schemes are PPT by the paper's convention (p.13)
--   - reading: in particular, whenever pre-challenge security is achievable, it is strictly weaker than adaptive security → Sec^ad(F) ⊆ Sec^na(F), and if some efficient scheme is in Sec^na(F) then some efficient scheme is in Sec^na(F) but not in Sec^ad(F); reason: asymptotic strictness of §2.3, p.15, with the inclusion of §3.2, p.16
--   - encoding: the common message space M_λ → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 2, p.17

import Mathlib
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_FamilyValidM
import Definitions.Def_RestrictedDec_Supplement_SecM
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 2** (pre-challenge security is strictly weaker than adaptive security). Let `M` be a
common message space and `𝓕` a valid family. Suppose `𝓕` contains an efficiently specified
function `F*` and uniformly computable valid equal-length messages `u₀, u₁` with
`F*(u₀) ≠ F*(u₁)`: one polynomial-time machine maps `1^λ` to an admissible description `d(λ)` and
to `u₀(λ), u₁(λ) ∈ M_λ` with `|u₀(λ)| = |u₁(λ)|` and `F*_{d(λ)}(u₀(λ)) ≠ F*_{d(λ)}(u₁(λ))`, for
every `λ`. Then
1. from every efficient scheme `E ∈ Sec^na(𝓕)` one obtains an efficient scheme
   `E† ∈ Sec^na(𝓕) \ Sec^ad(𝓕)`;
2. in particular, `Sec^ad(𝓕) ⊆ Sec^na(𝓕)`, and whenever `Sec^na(𝓕)` contains an efficient scheme,
   some efficient scheme is in `Sec^na(𝓕)` but not in `Sec^ad(𝓕)`, so the inclusion is strict.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 2, p.17; the timing
inclusion of §3.2, p.16. -/
theorem theorem_2 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M) (F : Family)
    (hF : FamilyValidM M F)
    (hstar : ∃ w : Str → Str, PolyTimeComputable w ∧ ∀ lam, ∃ d u0 u1 : Str,
      w (encNat lam) = BeyondDS.tup [d, u0, u1] ∧ F.admissible lam d = true ∧
      M lam u0 ∧ M lam u1 ∧ u0.length = u1.length ∧ F.eval lam d (some u0) ≠ F.eval lam d (some u1)) :
    (∀ E : PKE, IsSchemeM M E → SecM .na M F E →
      ∃ E' : PKE, IsSchemeM M E' ∧ SecM .na M F E' ∧ ¬ SecM .ad M F E') ∧
    ((∀ P : PKE, SecM .ad M F P → SecM .na M F P) ∧
      ((∃ E : PKE, IsSchemeM M E ∧ SecM .na M F E) →
        ∃ P : PKE, IsSchemeM M P ∧ SecM .na M F P ∧ ¬ SecM .ad M F P)) := by sorry

end Supplement

end RestrictedDec
