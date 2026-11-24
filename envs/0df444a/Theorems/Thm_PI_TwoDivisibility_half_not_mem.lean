-- Prove2me | Theorems.Thm_PI_TwoDivisibility_half_not_mem
-- name    : PI.TwoDivisibility.half_not_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:24.356584+00:00
-- url     : https://prove2.me/theorems/3697c700-89a1-46b1-86b0-e967d1e5280b
-- title:
--   Two Divisibility: half not mem
-- statement:
--   The Two Divisibility construction uses the half not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerCoordinatesZero/IntCoordsZero.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerCoordinatesZero/IntCoordsZero.lean#L14-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerCoordinatesZero_IntCoordsZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TwoDivisibility

theorem PI.TwoDivisibility.half_not_mem (L : PeriodPair) (p q : ℤ) (h : ¬ ((2 : ℤ) ∣ p ∧ (2 : ℤ) ∣ q)) :
    (p : ℂ) / 2 * L.ω₁ + (q : ℂ) / 2 * L.ω₂ ∉ L.lattice := by sorry
