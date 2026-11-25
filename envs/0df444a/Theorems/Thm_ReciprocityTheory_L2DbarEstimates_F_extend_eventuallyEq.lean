-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_extend_eventuallyEq
-- name    : ReciprocityTheory.L2DbarEstimates.F.extend_eventuallyEq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:56:24.747883+00:00
-- url     : https://prove2.me/theorems/15ee6c4f-cb5f-48ce-b635-4d6852aa59f5
-- title:
--   F: extend eventually Eq
-- statement:
--   The F construction uses the extend eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Extend.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Extend.lean#L19-L29

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Extend
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

theorem ReciprocityTheory.L2DbarEstimates.F.extend_eventuallyEq {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (he : IsChart n z e)
    (he' : IsChart n z e') (y : V n) (hy : y ∈ e'.target) (hs : e'.symm y ∈ e.source) :
    (e.source.indicator (G ∘ e) ∘ e'.symm) =ᶠ[𝓝 y] G := by sorry
