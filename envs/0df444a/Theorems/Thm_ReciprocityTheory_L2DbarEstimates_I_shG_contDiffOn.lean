-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_shG_contDiffOn
-- name    : ReciprocityTheory.L2DbarEstimates.I.shG_contDiffOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:05.057432+00:00
-- url     : https://prove2.me/theorems/29dce8c9-1301-4c7a-a420-d08b870f476d
-- title:
--   I: sh G cont Diff On
-- statement:
--   The I construction uses the sh G cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L22-L27

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.shG_contDiffOn {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) : ContDiffOn ℂ ∞ (shG n g e.symm) e.target := by sorry
