-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_tsupport_sub
-- name    : ReciprocityTheory.L2DbarEstimates.F.loc_tsupport_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:22.327556+00:00
-- url     : https://prove2.me/theorems/228fbc3d-1090-48b4-ad24-de3f07ff47ed
-- title:
--   F: loc tsupport sub
-- statement:
--   The F construction uses the loc tsupport sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L191-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L191-L195

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
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

theorem ReciprocityTheory.L2DbarEstimates.F.loc_tsupport_sub {M E : Type*} [TopologicalSpace M] [Zero E] (f : M → E) (T : Set M)
    (hT : IsClosed T) (h : ∀ x, x ∉ T → f x = 0) : tsupport f ⊆ T := by sorry
