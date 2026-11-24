-- Prove2me | Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_in_8b7430a5315f
-- name    : P2M_PI_QnLevBasicsW__Lev_apply_in_8b7430a5315f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:29:56.932564+00:00
-- url     : https://prove2.me/theorems/b5925b80-c47c-4ee9-878b-aa2ee412c9b9
-- title:
--   P2 M PI Qn Lev Basics W  Lev apply in 8b7430a5315f: P2 M PI Qn Lev Basics W  Lev apply in 8b7430a5315f
-- statement:
--   The P2 M PI Qn Lev Basics W  Lev apply in 8b7430a5315f construction uses the P2 M PI Qn Lev Basics W  Lev apply in 8b7430a5315f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L13-L22

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

theorem P2M_PI_QnLevBasicsW__Lev_apply_in_8b7430a5315f (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (a b : Fin (2 * r' + k + 1))
    (hp : p.val = a.val + i) (hq : q.val = b.val + i) : ιLev k i r' g p q = g a b := by sorry

alias «PI».«QnLevBasicsW».«ιLev_apply_in» := P2M_PI_QnLevBasicsW__Lev_apply_in_8b7430a5315f
