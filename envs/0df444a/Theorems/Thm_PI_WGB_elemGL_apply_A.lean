-- Prove2me | Theorems.Thm_PI_WGB_elemGL_apply_A
-- name    : PI.WGB.elemGL_apply_A
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:58:35.46367+00:00
-- url     : https://prove2.me/theorems/6fc455cf-be6c-5ef8-b7e8-06a99d05ec77
-- title:
--   WGB: elem GL apply A
-- statement:
--   The WGB construction uses the elem GL apply A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean#L62-L66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}

theorem PI.WGB.elemGL_apply_A (a b : Fin n) (hab : a ≠ b) (t : ℂ) (i j : Fin n) :
    ((elemGL_A a b hab t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j =
      (if i = j then 1 else 0) + (if a = i ∧ b = j then t else 0) := by sorry
