-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_levi_mul
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_levi_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:19.852025+00:00
-- url     : https://prove2.me/theorems/60cc4a48-644d-4447-a4cb-32e59a206e48
-- title:
--   I: evl levi mul
-- statement:
--   The I construction uses the evl levi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L24-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L24-L69

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.evl_levi_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℝ)
    (hf : CkR n z 2 f) (hg : CkR n z 2 g) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => f y * g y) x ξ =
      Levi n z f x ξ * (g x : ℂ) + (f x : ℂ) * Levi n z g x ξ +
        conj (dDot n z (fun y => (f y : ℂ)) x ξ) * dDot n z (fun y => (g y : ℂ)) x ξ +
        dDot n z (fun y => (f y : ℂ)) x ξ * conj (dDot n z (fun y => (g y : ℂ)) x ξ) := by sorry
