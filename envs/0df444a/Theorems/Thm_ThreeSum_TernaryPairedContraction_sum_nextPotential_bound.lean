-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedContraction_sum_nextPotential_bound
-- name    : ThreeSum.TernaryPairedContraction.sum_nextPotential_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:16.796764+00:00
-- url     : https://prove2.me/theorems/28794eae-4859-4e82-aa6b-271c39b25a93
-- title:
--   Ternary Paired Contraction: sum next Potential bound
-- statement:
--   The Ternary Paired Contraction construction uses the sum next Potential bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedContraction.lean#L55-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedContraction.lean#L55-L114

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedContraction
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {p : ℕ} [Fact p.Prime]
variable {E P : Type*} [Field E] [Algebra (ZMod p) E]
  [Fintype E] [DecidableEq E] [Fintype P]

theorem ThreeSum.TernaryPairedContraction.sum_nextPotential_bound {Λ L m F : ℕ} {α π : DigitType}
    (ℓ : E →ₗ[ZMod p] ZMod p) (hℓ : ℓ ≠ 0)
    (V : Submodule (ZMod p) (Fin Λ → ZMod p)) (hV : V ≠ ⊤) (hp : 3 ≤ p)
    (A : P → Matrix (Fin (m+m)) (Fin Λ) ℤ)
    (hsmall : ∀ a f, ((A a).submatrix id f).det.natAbs < p)
    (maps : Fin F → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (hsize1 : 8*Λ*p^2 ≤ Fintype.card E)
    (hsize : 8*Λ*p^(2*(m+m)) ≤ Fintype.card E) :
    p^(m+m) * (∑ seed ∈ admissible Λ ℓ V,
      nextPotential (α := α) (π := π) ℓ A maps seed) ≤
      3*(admissible Λ ℓ V).card*F*(vertices L π).card*
        (2^(π 1)*3^(π 2))^m*potential A := by sorry
