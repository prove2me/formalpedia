-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DiscEval_coeffPoly_bind__ea251764de75
-- name    : P2M_GlobalTheory_DiscEval_coeffPoly_bind__ea251764de75
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:56:34.139918+00:00
-- url     : https://prove2.me/theorems/2e0e3ad4-e422-5d01-b235-588da4d121b5
-- title:
--   P2 M Global Theory Disc Eval coeff Poly bind  ea251764de75: P2 M Global Theory Disc Eval coeff Poly bind  ea251764de75
-- statement:
--   The P2 M Global Theory Disc Eval coeff Poly bind  ea251764de75 construction uses the P2 M Global Theory Disc Eval coeff Poly bind  ea251764de75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L204-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L204-L211

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
variable {K : Type*} [Field K] {σ τ : Type*}

theorem P2M_GlobalTheory_DiscEval_coeffPoly_bind__ea251764de75 (m : ℤ) (g : σ → MvPolynomial τ K) (G : MvPolynomial σ K⸨X⸩) :
    coeffPoly m (bind₁ (fun k => map (HahnSeries.C : K →+* K⸨X⸩) (g k)) G) =
      bind₁ g (coeffPoly m G) := by sorry

alias «GlobalTheory».«DiscEval».«coeffPoly_bind₁» := P2M_GlobalTheory_DiscEval_coeffPoly_bind__ea251764de75
