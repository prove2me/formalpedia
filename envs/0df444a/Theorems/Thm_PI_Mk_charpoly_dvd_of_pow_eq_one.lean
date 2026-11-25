-- Prove2me | Theorems.Thm_PI_Mk_charpoly_dvd_of_pow_eq_one
-- name    : PI.Mk.charpoly_dvd_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:34:59.859385+00:00
-- url     : https://prove2.me/theorems/3128d22a-45d2-4d18-b567-89edab81db84
-- title:
--   Mk: charpoly dvd of pow eq one
-- statement:
--   The Mk construction uses the charpoly dvd of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L8-L24

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

theorem PI.Mk.charpoly_dvd_of_pow_eq_one {R : Type*} [CommRing R] {N : ℕ} (A : Matrix (Fin N) (Fin N) R)
    (n : ℕ) (h : A ^ n = 1) : A.charpoly ∣ (X ^ n - 1 : R[X]) ^ N := by sorry
