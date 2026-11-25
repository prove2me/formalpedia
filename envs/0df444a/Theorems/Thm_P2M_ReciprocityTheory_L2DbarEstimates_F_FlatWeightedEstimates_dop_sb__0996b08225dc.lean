-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_dop_sb__0996b08225dc
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_dop_sb__0996b08225dc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:52.942343+00:00
-- url     : https://prove2.me/theorems/6a988c03-4c9f-4f98-84df-cdfcd441a770
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates F Flat Weighted Estimates dop sb  0996b08225dc: P2 M Reciprocity Theory L2 Dbar Estimates F Flat Weighted Estimates dop sb  0996b08225dc
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates F Flat Weighted Estimates dop sb  0996b08225dc construction uses the P2 M Reciprocity Theory L2 Dbar Estimates F Flat Weighted Estimates dop sb  0996b08225dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L86-L90

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates

theorem P2M_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_dop_sb__0996b08225dc {n : ℕ} (j k : Fin n) (g : Fin 4 → V n → ℂ) (a b : V n → ℂ) (h0 : g 0 = a)
    (h1 : g 1 = a) (h2 : g 2 = b) (h3 : g 3 = b) (y : V n) :
    B.Dop cS (vS n j k) g y = wdb n j a y - wdb n k b y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«F».«FlatWeightedEstimates».«dop_sb'» := P2M_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_dop_sb__0996b08225dc
