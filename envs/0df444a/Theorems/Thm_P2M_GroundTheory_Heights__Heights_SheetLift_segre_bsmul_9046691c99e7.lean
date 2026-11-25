-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetLift_segre_bsmul_9046691c99e7
-- name    : P2M_GroundTheory_Heights__Heights_SheetLift_segre_bsmul_9046691c99e7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:22.733029+00:00
-- url     : https://prove2.me/theorems/0f1f0f11-6ee9-4115-83e9-7486e062a542
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Lift segre bsmul 9046691c99e7: P2 M Ground Theory Heights  Heights Sheet Lift segre bsmul 9046691c99e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Lift segre bsmul 9046691c99e7 construction uses the P2 M Ground Theory Heights  Heights Sheet Lift segre bsmul 9046691c99e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean#L33-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSheetLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_bsmul_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_update_eq

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
open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)
open GroundTheory.Heights₂.Heights.SheetLift
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SheetLift_segre_bsmul_9046691c99e7 (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (bsmul c z) = fun i => (∏ k, c k) * segre z i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetLift».«segre_bsmul» := P2M_GroundTheory_Heights__Heights_SheetLift_segre_bsmul_9046691c99e7
