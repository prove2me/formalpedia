-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_not_mem_neighborhood_of_ne
-- name    : ReciprocityTheory.L2DbarEstimates.I.not_mem_neighborhood_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:27.737492+00:00
-- url     : https://prove2.me/theorems/f012e291-8fab-4d55-b729-4b6edf6258a7
-- title:
--   I: not mem neighborhood of ne
-- statement:
--   The I construction uses the not mem neighborhood of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L46-L50

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.not_mem_neighborhood_of_ne {M : Type*} [TopologicalSpace M] (n : ℕ) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (W : M → Set M) (m : ℝ) (hL : IsLocalData n g ph r W m)
    {p q x : M} (hp : p ∈ zeroSet n g) (hq : q ∈ zeroSet n g) (hpq : q ≠ p) (hx : x ∈ W p) :
    x ∉ W q := by sorry
