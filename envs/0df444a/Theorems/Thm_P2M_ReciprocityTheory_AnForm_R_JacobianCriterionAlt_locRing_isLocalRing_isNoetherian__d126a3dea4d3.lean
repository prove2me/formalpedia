-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_locRing_isLocalRing_isNoetherian__d126a3dea4d3
-- name    : P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_locRing_isLocalRing_isNoetherian__d126a3dea4d3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:37.433839+00:00
-- url     : https://prove2.me/theorems/96efe673-79d3-4077-85ad-05db0627acfb
-- title:
--   P2 M Reciprocity Theory An Form R Jacobian Criterion Alt loc Ring is Local Ring is Noetherian  d126a3dea4d3: P2 M Reciprocity Theory An Form R Jacobian Criterion Alt loc Ring is Local Ring is Noetheri
-- statement:
--   The P2 M Reciprocity Theory An Form R Jacobian Criterion Alt loc Ring is Local Ring is Noetherian  d126a3dea4d3 construction uses the P2 M Reciprocity Theory An Form R Jacobian Criterion Alt loc Ring is Local Ring is Noetherian  d126a3dea4d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L156-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L156-L166

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
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

theorem P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_locRing_isLocalRing_isNoetherian__d126a3dea4d3 (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) : IsLocalRing (locR K p) ∧ IsNoetherianRing (locR K p) := by sorry

alias «ReciprocityTheory».«AnForm».«R».«JacobianCriterionAlt».«locRing_isLocalRing_isNoetherian'» := P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_locRing_isLocalRing_isNoetherian__d126a3dea4d3
