-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DiagRank_det_one_sub_p_ne
-- name    : PI.UnitaryGroupMassFormula.DiagRank.det_one_sub_p_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:53.121196+00:00
-- url     : https://prove2.me/theorems/a5d66836-554a-54f9-b87b-c2c7743bc3e6
-- title:
--   Diag Rank: det one sub p ne
-- statement:
--   The Diag Rank construction uses the det one sub p ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalRank/DetOneSubPNe.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalRank/DetOneSubPNe.lean#L9-L19

import Definitions.Def_Formalism_PeriodIntegrals_DiagRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalRank_DetOneSubPNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DiagRank
open Finset

theorem PI.UnitaryGroupMassFormula.DiagRank.det_one_sub_p_ne {p : ℕ} [Fact p.Prime] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ_[p]) :
    (1 - (p : ℤ_[p]) • M).det ≠ 0 := by sorry
