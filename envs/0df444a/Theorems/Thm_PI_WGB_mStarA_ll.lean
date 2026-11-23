-- Prove2me | Theorems.Thm_PI_WGB_mStarA_ll
-- name    : PI.WGB.mStarA_ll
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:41.892833+00:00
-- url     : https://prove2.me/theorems/25953a05-8d21-4f0e-90a4-7f4862e4d51a
-- title:
--   WGB: m Star A ll
-- statement:
--   The WGB construction uses the m Star A ll property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L30-L32

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

theorem PI.WGB.mStarA_ll (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) :
    mStarA kap ν (Fin.last n, Fin.last n) = ν (Fin.last n) := by sorry
