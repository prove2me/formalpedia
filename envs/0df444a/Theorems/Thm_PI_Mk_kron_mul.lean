-- Prove2me | Theorems.Thm_PI_Mk_kron_mul
-- name    : PI.Mk.kron_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:19.678871+00:00
-- url     : https://prove2.me/theorems/eb01f40c-8ba3-409a-858c-e31c39d6241d
-- title:
--   Mk: kron mul
-- statement:
--   The Mk construction uses the kron mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/PowerSum.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/PowerSum.lean#L51-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Matrix Finset

theorem PI.Mk.kron_mul {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) (A B : Matrix n n ℤ) :
    kron k (A * B) = kron k A * kron k B := by sorry
