-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_col_fix
-- name    : PI.QnLevBasicsW.col_fix
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:33.431397+00:00
-- url     : https://prove2.me/theorems/85a02d7e-1f1c-467f-8300-a73e1a4a0d57
-- title:
--   Qn Lev Basics W: col fix
-- statement:
--   The Qn Lev Basics W construction uses the col fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L67-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L67-L84

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}

theorem PI.QnLevBasicsW.col_fix (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (q : Fin (2 * (i + r') + k + 1))
    (h : ∀ a : Fin (2 * r' + k + 1), q.val = a.val + i → g *ᵥ bvec a = bvec a) :
    ιLev k i r' g *ᵥ bvec q = bvec q := by sorry
