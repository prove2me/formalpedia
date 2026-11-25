-- Prove2me | Theorems.Thm_PI_WGB_eval_rowAct_A
-- name    : PI.WGB.eval_rowAct_A
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:46:09.657849+00:00
-- url     : https://prove2.me/theorems/b1cd70b6-c5b8-4357-86f8-a54393755ee5
-- title:
--   WGB: eval row Act A
-- statement:
--   The WGB construction uses the eval row Act A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean#L39-L48

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

theorem PI.WGB.eval_rowAct_A {r c : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (x : Fin r × Fin c → ℂ)
    (f : MvPolynomial (Fin r × Fin c) ℂ) :
    eval x (rowAct ℂ M f) = eval (fun v => ∑ b, M v.1 b * x (b, v.2)) f := by sorry
