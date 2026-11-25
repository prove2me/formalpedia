-- Prove2me | Theorems.Thm_PI_WhitFunctDualWork_stable_of_irreducible
-- name    : PI.WhitFunctDualWork.stable_of_irreducible
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:35.645468+00:00
-- url     : https://prove2.me/theorems/d6f16a0d-8f5d-4a19-8b81-eee3943dad48
-- title:
--   Whit Funct Dual Work: stable of irreducible
-- statement:
--   The Whit Funct Dual Work construction uses the stable of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WhittakerFunctionalDual/StableOfIrreducible.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WhittakerFunctionalDual/StableOfIrreducible.lean#L8-L23

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

theorem PI.WhitFunctDualWork.stable_of_irreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, π g x ∈ W) → W = ⊥ ∨ W = ⊤ := by sorry
