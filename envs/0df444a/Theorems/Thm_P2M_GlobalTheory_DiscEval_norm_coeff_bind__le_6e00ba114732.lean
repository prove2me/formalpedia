-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DiscEval_norm_coeff_bind__le_6e00ba114732
-- name    : P2M_GlobalTheory_DiscEval_norm_coeff_bind__le_6e00ba114732
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:58:44.483168+00:00
-- url     : https://prove2.me/theorems/a1282c97-410a-4a84-a2fb-f4aca605a698
-- title:
--   P2 M Global Theory Disc Eval norm coeff bind  le 6e00ba114732: P2 M Global Theory Disc Eval norm coeff bind  le 6e00ba114732
-- statement:
--   The P2 M Global Theory Disc Eval norm coeff bind  le 6e00ba114732 construction uses the P2 M Global Theory Disc Eval norm coeff bind  le 6e00ba114732 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L259-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L259-L276

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
open MvPolynomial
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]

theorem P2M_GlobalTheory_DiscEval_norm_coeff_bind__le_6e00ba114732 {K : Type*} [NormedField K] [IsUltrametricDist K] {σ τ : Type*}
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) (hP1 : ∀ μ, ‖coeff μ P‖ ≤ 1)
    {g : σ → MvPolynomial τ K} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ k μ, ‖coeff μ (g k)‖ ≤ c)
    (μ : τ →₀ ℕ) : ‖coeff μ (bind₁ g P)‖ ≤ c ^ d := by sorry

alias «GlobalTheory».«DiscEval».«norm_coeff_bind₁_le» := P2M_GlobalTheory_DiscEval_norm_coeff_bind__le_6e00ba114732
