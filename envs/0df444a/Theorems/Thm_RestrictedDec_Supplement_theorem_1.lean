-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_1
-- name    : RestrictedDec.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:35:04.684099+00:00
-- url     : https://prove2.me/theorems/37d1fe80-22b5-499c-b8f0-2357887e96d1
-- title:
--   Theorem 1 — an IND-CPA scheme that is not $\mathrm{IND}^{na}_{\mathcal F}$-secure, from a separating pair in $M_\perp$
-- statement:
--   Let $M$ be a common message space containing two efficiently found distinct equal-length messages, and let $\mathcal F$ be a valid family of permitted functions over $M$. Suppose $\mathcal F$ contains a uniformly computable nonconstant function $F^\star$ with an efficiently findable separating pair: one polynomial-time machine computes from $1^\lambda$ an admissible description of $F^\star$ and elements $\tau_0,\tau_1\in M_\perp=M_\lambda\cup\{\bot\}$ with
--   $$F^\star(\tau_0)\neq F^\star(\tau_1).$$
--   If an efficient, ordinarily correct, IND-CPA-secure public-key encryption scheme over $M$ exists, then there is an efficient, ordinarily correct public-key encryption scheme $\Pi'$ over $M$ such that
--   $$\Pi'\ \text{is IND-CPA secure}\qquad\text{and}\qquad \Pi'\notin\mathrm{Sec}^{na}(\mathcal F).$$
--   Since $\Pi'$ is correct, the second property says that some uniform PPT pre-challenge adversary has non-negligible advantage.
--
--   The theorem shows that pre-challenge functional decryption leakage is a genuinely stronger requirement than CPA security as soon as one permitted function separates two decryption outputs: decryption branches never reached by honest encryption are invisible to a CPA adversary but can leak the secret key through the oracle.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: a scheme exists / one can construct a scheme → an efficient scheme (IsSchemeM) exists; reason: schemes are uniform PPT algorithms by the paper's convention (p.13, p.15); an inefficient witness would not be a scheme
--   - encoding: F contains a uniformly computable nonconstant F* with an efficiently findable separating pair → one polynomial-time machine outputs, for every λ, an admissible description d(λ) and τ₀(λ), τ₁(λ) ∈ M_⊥ with F*_{d(λ)}(τ₀) ≠ F*_{d(λ)}(τ₁); reason: the uniformity convention of §2.3, p.15; τ_b ∈ M_⊥ as in the proof, p.16
--   - reading: an IND-CPA-secure public-key encryption scheme exists over M_λ; Π′ is IND-CPA secure but not IND^na_F-secure → ∃ E efficient, ordinarily correct (Definition 3) and IND-CPA; the witness Π′ is efficient, ordinarily correct, IND-CPA and ∉ Sec^na(F); reason: the proof uses 'ordinary correctness of Π' (p.17) and its Π′ inherits it; without correctness of Π′ the claim would hold for any IND-CPA scheme with a broken decryption, since Sec^na(F) contains correctness (Definition 1)
--   - encoding: the common message space M_λ with two efficiently found distinct equal-length messages → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 1, p.16

import Mathlib
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_FamilyValidM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_INDCPAM
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 1** (IND-CPA does not give pre-challenge functional security). Let `M` be a common
message space and `𝓕` a valid family of permitted functions. Suppose `𝓕` contains a uniformly
computable nonconstant function `F*` with an efficiently findable separating pair: one
polynomial-time machine maps `1^λ` to an admissible description `d(λ)` and to
`τ₀(λ), τ₁(λ) ∈ M_⊥` with `F*_{d(λ)}(τ₀(λ)) ≠ F*_{d(λ)}(τ₁(λ))`, for every `λ`. If an efficient,
ordinarily correct, IND-CPA-secure public-key encryption scheme over `M` exists, then some
efficient, ordinarily correct public-key encryption scheme `Π′` over `M` is IND-CPA secure but not
`IND^na_𝓕`-secure.
Nguyen–Susilo, *Between CPA and CCA: Security Hierarchies for Restricted Decryption*, STOC 2027
submission (manuscript sha256 6aeac40c…), Theorem 1, p.16.

**Formalization Note.** `τ_b` is passed as `encOpt τ_b` (`⊥` allowed). "Exists" means an efficient
(`IsSchemeM`) scheme. `IND^na_𝓕` contains ordinary correctness (Definition 1), so `Π′` is required
to be correct: otherwise any IND-CPA scheme with a broken decryption would witness the claim. The
proof's `Π′` inherits correctness from `Π`, whose correctness the proof uses (p.17). -/
theorem theorem_1 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M) (F : Family)
    (hF : FamilyValidM M F)
    (hstar : ∃ w : Str → Str, PolyTimeComputable w ∧ ∀ lam, ∃ (d : Str) (τ0 τ1 : Option Str),
      w (encNat lam) = BeyondDS.tup [d, encOpt τ0, encOpt τ1] ∧ F.admissible lam d = true ∧
      (∀ m, τ0 = some m → M lam m) ∧ (∀ m, τ1 = some m → M lam m) ∧
      F.eval lam d τ0 ≠ F.eval lam d τ1)
    (hCPA : ∃ E : PKE, IsSchemeM M E ∧ CorrectM M E ∧ INDCPAM M E) :
    ∃ P : PKE, IsSchemeM M P ∧ CorrectM M P ∧ INDCPAM M P ∧ ¬ SecM .na M F P := by sorry

end Supplement

end RestrictedDec
