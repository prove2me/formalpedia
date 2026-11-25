-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_sum_offDiag
-- name    : PI.SqfDivDeg.W.sum_offDiag
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:36.497204+00:00
-- url     : https://prove2.me/theorems/85e99830-baac-4ce7-ab54-b4db8fe1a926
-- title:
--   W: sum off Diag
-- statement:
--   The W construction uses the sum off Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L98-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L98-L109

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical

theorem PI.SqfDivDeg.W.sum_offDiag {g : ℕ} [Fact g.Prime] (S : Finset (ZMod g)[X]) :
    ∑ f ∈ S, (rts f).offDiag.card =
      ∑ x ∈ (univ : Finset (ZMod g)).offDiag,
        (S.filter (fun f => f.IsRoot x.1 ∧ f.IsRoot x.2)).card := by sorry
