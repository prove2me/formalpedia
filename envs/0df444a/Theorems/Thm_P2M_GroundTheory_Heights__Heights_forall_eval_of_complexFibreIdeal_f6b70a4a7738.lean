-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_forall_eval_of_complexFibreIdeal_f6b70a4a7738
-- name    : P2M_GroundTheory_Heights__Heights_forall_eval_of_complexFibreIdeal_f6b70a4a7738
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:11.059534+00:00
-- url     : https://prove2.me/theorems/9b7900b4-fa27-44e1-8a4d-6dc49df98ab5
-- title:
--   P2 M Ground Theory Heights  Heights forall eval of complex Fibre Ideal f6b70a4a7738: P2 M Ground Theory Heights  Heights forall eval of complex Fibre Ideal f6b70a4a7738
-- statement:
--   The P2 M Ground Theory Heights  Heights forall eval of complex Fibre Ideal f6b70a4a7738 construction uses the P2 M Ground Theory Heights  Heights forall eval of complex Fibre Ideal f6b70a4a7738 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetParam.lean#L54-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetParam.lean#L54-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_forall_eval_of_complexFibreIdeal_f6b70a4a7738 {P : Ideal (MRing (PBlk n))} {z : Fin n → ℂ}
    (hz : ∀ q ∈ complexFibreIdeal P, eval z q = 0) :
    ∀ f ∈ P, eval (fun p : Σ k, PBlk n k => z p.2) (map (Int.castRingHom ℂ) f) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«forall_eval_of_complexFibreIdeal» := P2M_GroundTheory_Heights__Heights_forall_eval_of_complexFibreIdeal_f6b70a4a7738
