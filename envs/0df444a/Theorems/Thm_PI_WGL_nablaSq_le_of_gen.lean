-- Prove2me | Theorems.Thm_PI_WGL_nablaSq_le_of_gen
-- name    : PI.WGL.nablaSq_le_of_gen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:47:16.667847+00:00
-- url     : https://prove2.me/theorems/34dbfaa2-6c8e-4bf4-9106-5ce81118fb8b
-- title:
--   WGL: nabla Sq le of gen
-- statement:
--   The WGL construction uses the nabla Sq le of gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/NablaSqLeOfGen.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/NablaSqLeOfGen.lean#L10-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_NablaSqLeOfGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGL.nablaSq_le_of_gen (h4 : PI.GTBranch) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N)
    (P : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hP : ∀ (mu : DomWeight n), Interlace h lam mu →
      ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
        ∀ s ∈ nablaSq ℂ n mu, φ s ∈ P) :
    nablaSq ℂ N lam ≤ P := by sorry
