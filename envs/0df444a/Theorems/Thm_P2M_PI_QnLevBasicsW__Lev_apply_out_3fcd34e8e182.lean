-- Prove2me | Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_out_3fcd34e8e182
-- name    : P2M_PI_QnLevBasicsW__Lev_apply_out_3fcd34e8e182
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:27:55.867804+00:00
-- url     : https://prove2.me/theorems/c0841a3d-527b-4bea-8009-8f36f204e936
-- title:
--   P2 M PI Qn Lev Basics W  Lev apply out 3fcd34e8e182: P2 M PI Qn Lev Basics W  Lev apply out 3fcd34e8e182
-- statement:
--   The P2 M PI Qn Lev Basics W  Lev apply out 3fcd34e8e182 construction uses the P2 M PI Qn Lev Basics W  Lev apply out 3fcd34e8e182 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L24-L28

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

theorem P2M_PI_QnLevBasicsW__Lev_apply_out_3fcd34e8e182 (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) :
    ιLev k i r' g p q = if p = q then 1 else 0 := by sorry

alias «PI».«QnLevBasicsW».«ιLev_apply_out» := P2M_PI_QnLevBasicsW__Lev_apply_out_3fcd34e8e182
