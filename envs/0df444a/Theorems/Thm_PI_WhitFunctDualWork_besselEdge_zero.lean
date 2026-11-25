-- Prove2me | Theorems.Thm_PI_WhitFunctDualWork_besselEdge_zero
-- name    : PI.WhitFunctDualWork.besselEdge_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:12.660549+00:00
-- url     : https://prove2.me/theorems/8f823a91-515e-5709-816d-9c3e707c82fd
-- title:
--   Whit Funct Dual Work: bessel Edge zero
-- statement:
--   The Whit Funct Dual Work construction uses the bessel Edge zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WhittakerFunctionalDual/StableOfIrreducible.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WhittakerFunctionalDual/StableOfIrreducible.lean#L44-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WhitFunctDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WhittakerFunctionalDual_StableOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WhitFunctDualWork
open Formalism.L2.SG.GGMirabolic

theorem PI.WhitFunctDualWork.besselEdge_zero (i j : ℕ) : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge 0 0 i j ↔ j = i + 1 := by sorry
