-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_eval_torus
-- name    : ReciprocityTheory.MultiplicativeHeights.continuous_eval_torus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:28.748137+00:00
-- url     : https://prove2.me/theorems/043bccfe-ac19-4de8-9d5f-bb8bbd990417
-- title:
--   Multiplicative Heights: continuous eval torus
-- statement:
--   The Multiplicative Heights construction uses the continuous eval torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L122-L124

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.MultiplicativeHeights.continuous_eval_torus (f : MvPolynomial ι ℂ) :
    Continuous fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f := by sorry
