-- Prove2me | Theorems.Thm_PI_IsoFunVW_finite_oe
-- name    : PI.IsoFunVW.finite_oe
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:10:00.432688+00:00
-- url     : https://prove2.me/theorems/a4a644ba-acda-4fbe-b026-78cd1e6393e2
-- title:
--   Iso Fun VW: finite oe
-- statement:
--   The Iso Fun VW construction uses the finite oe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/DetSubmatrixNoninj.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/DetSubmatrixNoninj.lean#L7-L9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Equiv
open PI PI.IsoFunVW

theorem PI.IsoFunVW.finite_oe (m n : ℕ) : Finite (Fin m ↪o Fin n) := by sorry
