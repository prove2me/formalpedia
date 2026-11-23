-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_jac
-- name    : ReciprocityTheory.L2DbarEstimates.I.sh_jac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:34.346617+00:00
-- url     : https://prove2.me/theorems/590eb7aa-5a6e-4dd0-9f7d-822accb575bf
-- title:
--   I: sh jac
-- statement:
--   The I construction uses the sh jac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L38-L57

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

theorem ReciprocityTheory.L2DbarEstimates.I.sh_jac {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (y : V n) (hy : y ∈ e.target) :
    jac n z g (e.symm y) = LinearMap.det (fderiv ℂ (shG n g e.symm) y : V n →ₗ[ℂ] V n) := by sorry
