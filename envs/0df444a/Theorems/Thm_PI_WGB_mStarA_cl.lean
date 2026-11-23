-- Prove2me | Theorems.Thm_PI_WGB_mStarA_cl
-- name    : PI.WGB.mStarA_cl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:47.750678+00:00
-- url     : https://prove2.me/theorems/900c664d-6a67-4a75-a78b-c135f53f221c
-- title:
--   WGB: m Star A cl
-- statement:
--   The WGB construction uses the m Star A cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L22-L24

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

theorem PI.WGB.mStarA_cl (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (a : Fin n) :
    mStarA kap ν (Fin.castSucc a, Fin.last n) = 0 := by sorry
