-- Prove2me | Theorems.Thm_PI_WhitFunctDualWork_isIrr_dual
-- name    : PI.WhitFunctDualWork.isIrr_dual
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:21.922824+00:00
-- url     : https://prove2.me/theorems/65a145b9-d2b0-52de-81b7-cd6b24949422
-- title:
--   Whit Funct Dual Work: is Irr dual
-- statement:
--   The Whit Funct Dual Work construction uses the is Irr dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WhittakerFunctionalDual/StableOfIrreducible.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WhittakerFunctionalDual/StableOfIrreducible.lean#L25-L42

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

theorem PI.WhitFunctDualWork.isIrr_dual {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr (Representation.dual π) := by sorry
