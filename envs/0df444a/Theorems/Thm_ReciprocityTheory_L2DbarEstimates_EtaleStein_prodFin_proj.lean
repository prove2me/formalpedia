-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_EtaleStein_prodFin_proj
-- name    : ReciprocityTheory.L2DbarEstimates.EtaleStein.prodFin_proj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:19.501364+00:00
-- url     : https://prove2.me/theorems/e69259dc-98fb-57cb-b017-12ad0132cbe8
-- title:
--   Etale Stein: prod Fin proj
-- statement:
--   The Etale Stein construction uses the prod Fin proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L190-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L190-L192

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

theorem ReciprocityTheory.L2DbarEstimates.EtaleStein.prodFin_proj {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (X : EtaleStein n M)
    (p : ℕ) : (EtaleStein.prodFin n X p).z = fun q => X.z q.1 := by sorry
