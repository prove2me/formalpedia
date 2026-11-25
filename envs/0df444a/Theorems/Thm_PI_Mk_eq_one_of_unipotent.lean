-- Prove2me | Theorems.Thm_PI_Mk_eq_one_of_unipotent
-- name    : PI.Mk.eq_one_of_unipotent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:00.663867+00:00
-- url     : https://prove2.me/theorems/713094e4-9125-5fef-b400-06843dbdf09d
-- title:
--   Mk: eq one of unipotent
-- statement:
--   The Mk construction uses the eq one of unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L131-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L131-L154

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix

theorem PI.Mk.eq_one_of_unipotent {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (n : ℕ) (hn : 0 < n)
    (h : A ^ n = 1) (hu : (A - 1) ^ N = 0) : A = 1 := by sorry
