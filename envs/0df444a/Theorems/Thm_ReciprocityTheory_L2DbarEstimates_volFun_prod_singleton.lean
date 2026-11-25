-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_volFun_prod_singleton
-- name    : ReciprocityTheory.L2DbarEstimates.volFun_prod_singleton
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:02:01.912799+00:00
-- url     : https://prove2.me/theorems/0b98c201-5bf8-5cb7-bc24-5a28bd6e0b18
-- title:
--   L2 Dbar Estimates: vol Fun prod singleton
-- statement:
--   The L2 Dbar Estimates construction uses the vol Fun prod singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L126-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L126-L139

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.volFun_prod_singleton {M : Type*} (n : ℕ) (z : M → V n) (p : ℕ) (B : Set M) (i : Fin p) :
    volFun n (fun q : M × Fin p => z q.1) (B ×ˢ {i}) = volFun n z B := by sorry
