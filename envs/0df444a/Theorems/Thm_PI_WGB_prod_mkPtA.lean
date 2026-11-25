-- Prove2me | Theorems.Thm_PI_WGB_prod_mkPtA
-- name    : PI.WGB.prod_mkPtA
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:46:25.579363+00:00
-- url     : https://prove2.me/theorems/8fd08ba6-122e-428f-bb20-d4d5af17c500
-- title:
--   WGB: prod mk Pt A
-- statement:
--   The WGB construction uses the prod mk Pt A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L145-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L145-L154

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
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

theorem PI.WGB.prod_mkPtA (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) :
    ∏ v, mkPtA dv z v ^ (mStarA kap ν) v =
      (∏ a, dv a ^ kap a) * (∏ k : Fin n, z (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k)) *
        z (Fin.last n) ^ ν (Fin.last n) := by sorry
