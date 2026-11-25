-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_kPsi_inner
-- name    : ReciprocityTheory.L2DbarEstimates.F.kPsi_inner
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:22.508942+00:00
-- url     : https://prove2.me/theorems/eae17f90-1826-505c-8a93-2c6b4632bef5
-- title:
--   F: k Psi inner
-- statement:
--   The F construction uses the k Psi inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/KPsiHasCompactSupport.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/KPsiHasCompactSupport.lean#L35-L45

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
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

theorem ReciprocityTheory.L2DbarEstimates.F.kPsi_inner {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (φ : M → ℂ) (j k : Fin n) (v : V n) (x : M) :
    (ENNReal.ofReal (Real.exp (-ph x))).toReal • ⟪kPsi n z ph φ j k x, v⟫_ℂ =
      v k * db n z j φ x - v j * db n z k φ x := by sorry
