-- Prove2me | Theorems.Thm_PI_StabSplit_Alg_unitK
-- name    : PI.StabSplit.Alg.unitK
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:26.020245+00:00
-- url     : https://prove2.me/theorems/6399e00f-720f-4ef2-a2ba-c524a740fea4
-- title:
--   Alg: unit K
-- statement:
--   The Alg construction uses the unit K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/UnitR.lean#L70-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/UnitR.lean#L70-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.StabSplit PI.StabSplit.Alg
variable {R : Type*} [Ring R]
variable [StarRing R]

theorem PI.StabSplit.Alg.unitK (H P h : R) (hH : star H = H) (hPH : star P * H = H * P) (hPP : P * P = P)
    (hh : star h * H * h = H) (hU : P * h * (1 - P) = 0) :
    star (h * (1 - P) + P) * H * (h * (1 - P) + P) = H := by sorry
