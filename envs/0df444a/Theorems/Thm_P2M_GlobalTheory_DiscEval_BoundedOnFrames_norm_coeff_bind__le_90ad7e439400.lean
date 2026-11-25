-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_bind__le_90ad7e439400
-- name    : P2M_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_bind__le_90ad7e439400
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:03:52.851006+00:00
-- url     : https://prove2.me/theorems/8c57a125-2277-4475-9958-9fd6fe81f268
-- title:
--   P2 M Global Theory Disc Eval Bounded On Frames norm coeff bind  le 90ad7e439400: P2 M Global Theory Disc Eval Bounded On Frames norm coeff bind  le 90ad7e439400
-- statement:
--   The P2 M Global Theory Disc Eval Bounded On Frames norm coeff bind  le 90ad7e439400 construction uses the P2 M Global Theory Disc Eval Bounded On Frames norm coeff bind  le 90ad7e439400 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L792-L801
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L792-L801

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
variable (p : ℕ) [Fact p.Prime]
variable {p}
open MvPolynomial
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
variable {i hi hπ} {F : MvPolynomial (EntryIndex n n) A}

theorem P2M_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_bind__le_90ad7e439400 (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {τ : Type*} {g : EntryIndex n n → MvPolynomial τ ℂ_[p]} {c : ℝ}
    (hc : 0 ≤ c) (hg : ∀ k μ, ‖coeff μ (g k)‖ ≤ c) (μ : τ →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => map HahnSeries.C (g k)) (map (laurent π A i hπ) F))).coeff m‖ ≤
        c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => map HahnSeries.C (g k))
        (map (laurent π A i hπ) F))).coeff m = 0) := by sorry

alias «GlobalTheory».«DiscEval».«BoundedOnFrames».«norm_coeff_bind₁_le» := P2M_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_bind__le_90ad7e439400
