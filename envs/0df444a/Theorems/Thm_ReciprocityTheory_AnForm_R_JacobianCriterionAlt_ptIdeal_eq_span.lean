-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_ptIdeal_eq_span
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ptIdeal_eq_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:24.796392+00:00
-- url     : https://prove2.me/theorems/cff8e51d-d3a4-43c2-b10d-65f99b31246e
-- title:
--   Jacobian Criterion Alt: pt Ideal eq span
-- statement:
--   The Jacobian Criterion Alt construction uses the pt Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L55-L63

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ptIdeal_eq_span (p : Fin n → ℂ) :
    ptI p = Ideal.span (Set.range fun i => X i - C (p i)) := by sorry
