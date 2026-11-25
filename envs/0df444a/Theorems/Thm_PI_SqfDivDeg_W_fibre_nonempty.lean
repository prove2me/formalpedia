-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_fibre_nonempty
-- name    : PI.SqfDivDeg.W.fibre_nonempty
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:25:17.836359+00:00
-- url     : https://prove2.me/theorems/205f5c79-f729-43e2-b227-db37bb69120e
-- title:
--   W: fibre nonempty
-- statement:
--   The W construction uses the fibre nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/FibreNonempty.lean#L39-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/FibreNonempty.lean#L39-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_FibreNonempty
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

theorem PI.SqfDivDeg.W.fibre_nonempty {g r a : ℕ} [Fact g.Prime] (har : a ≤ r) {f : (ZMod g)[X]}
    (hf : PI.SqfLab.Eiv g r a f) :
    ∃ q h, q ∈ Mon g a ∧ h ∈ Mon g (r - a) ∧ q * h = f := by sorry
