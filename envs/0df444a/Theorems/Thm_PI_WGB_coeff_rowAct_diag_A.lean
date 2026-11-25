-- Prove2me | Theorems.Thm_PI_WGB_coeff_rowAct_diag_A
-- name    : PI.WGB.coeff_rowAct_diag_A
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:46:18.55909+00:00
-- url     : https://prove2.me/theorems/fbf8361a-44c7-4399-8243-6483b94c111d
-- title:
--   WGB: coeff row Act diag A
-- statement:
--   The WGB construction uses the coeff row Act diag A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean#L125-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean#L125-L137

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

theorem PI.WGB.coeff_rowAct_diag_A {r c : ℕ} (s : Fin r → ℂ) (f : MvPolynomial (Fin r × Fin c) ℂ)
    (m : Fin r × Fin c →₀ ℕ) :
    coeff m (rowAct ℂ (Matrix.diagonal s) f) = (∏ ρ, s ρ ^ (∑ j : Fin c, m (ρ, j))) * coeff m f := by sorry
