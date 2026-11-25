-- Prove2me | Theorems.Thm_PI_KerTens_W_upd_part
-- name    : PI.KerTens.W.upd_part
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:33:42.435382+00:00
-- url     : https://prove2.me/theorems/3553f7b4-d988-554f-8c0a-6bf15fdd2908
-- title:
--   W: upd part
-- statement:
--   The W construction uses the upd part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorSpanning/MatHHOne.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorSpanning/MatHHOne.lean#L48-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open PI PI.KerTens PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)

theorem PI.KerTens.W.upd_part {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) :
    upd z b (part z b) = z := by sorry
