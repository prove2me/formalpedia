-- Prove2me | Theorems.Thm_PI_WGL_BrInt_rat_of_pairings
-- name    : PI.WGL.BrInt.rat_of_pairings
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:45:33.930132+00:00
-- url     : https://prove2.me/theorems/5322a808-d295-434a-9ddb-adf235f9dd25
-- title:
--   Br Int: rat of pairings
-- statement:
--   The Br Int construction uses the rat of pairings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ConstructionBrInt.lean#L69-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ConstructionBrInt.lean#L69-L131

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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
open Formalism.BasicNotions MvPolynomial
open PI.WGL.BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
variable {σ : Type}

theorem PI.WGL.BrInt.rat_of_pairings {ι : Type*} [Fintype ι] (β : ι → MvPolynomial σ ℚ) (G : MvPolynomial σ ℂ)
    (hG : G ∈ Submodule.span ℂ (Set.range fun i => map (algebraMap ℚ ℂ) (β i)))
    (hq : ∀ i, ∃ q : ℚ, fockF (map (algebraMap ℚ ℂ) (β i)) G = (q : ℂ)) :
    ∃ G0 ∈ Submodule.span ℚ (Set.range β), G = map (algebraMap ℚ ℂ) G0 := by sorry
