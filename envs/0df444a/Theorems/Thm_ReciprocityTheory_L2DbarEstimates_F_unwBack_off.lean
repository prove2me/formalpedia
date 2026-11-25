-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unwBack_off
-- name    : ReciprocityTheory.L2DbarEstimates.F.unwBack_off
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:16.976969+00:00
-- url     : https://prove2.me/theorems/0ebf517f-3b2b-4e3d-a0a0-a7bf8bfeee0f
-- title:
--   F: unw Back off
-- statement:
--   The F construction uses the unw Back off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L152-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L152-L181

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

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

theorem ReciprocityTheory.L2DbarEstimates.F.unwBack_off {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (K0 : Set M) (hK0 : IsCompact K0) (u : M → ℂ) (hu : ∀ x, x ∉ K0 → u x = 0) (x : M)
    (hx : x ∉ K0) (j : Fin n) : d n z j u x = 0 ∧ db n z j u x = 0 := by sorry
