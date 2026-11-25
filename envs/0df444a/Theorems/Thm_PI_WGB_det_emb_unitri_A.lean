-- Prove2me | Theorems.Thm_PI_WGB_det_emb_unitri_A
-- name    : PI.WGB.det_emb_unitri_A
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:54.453388+00:00
-- url     : https://prove2.me/theorems/8e176dda-1807-5449-8bd7-2dec693d2577
-- title:
--   WGB: det emb unitri A
-- statement:
--   The WGB construction uses the det emb unitri A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean#L35-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Theorems.Thm_UpperTheory_Reformulated_B_Qe13_det_emb_unitri_A

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

theorem PI.WGB.det_emb_unitri_A (g : GL (Fin n) ℂ) (hl : ∀ i j, j < i → g i j = 0) (hd : ∀ i, g i i = 1) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = 1 := by sorry
