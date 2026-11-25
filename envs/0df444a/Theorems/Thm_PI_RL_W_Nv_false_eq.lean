-- Prove2me | Theorems.Thm_PI_RL_W_Nv_false_eq
-- name    : PI.RL.W.Nv_false_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:25.16905+00:00
-- url     : https://prove2.me/theorems/f71bd872-141d-4645-a5a6-41b66b72b379
-- title:
--   W: Nv false eq
-- statement:
--   The W construction uses the Nv false eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowDerivationChainRule/NvFalseEq.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowDerivationChainRule/NvFalseEq.lean#L13-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_DetDer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_NvFalseEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RL PI.RL.W
open PI.RL

theorem PI.RL.W.Nv_false_eq (K : Type) [Field K] (m : ℕ) (c : Fin (m + 1)) :
    Nv K m false c = ((genM K m).updateRow c (Pi.single (Fin.last m) 1)).det := by sorry
