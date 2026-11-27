-- Prove2me | Theorems.Thm_PI_FGTFG_main
-- name    : PI.FGTFG.main
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:19.613912+00:00
-- url     : https://prove2.me/theorems/44f3d300-a9a3-4ade-b23b-58e8fbbae4c8
-- title:
--   FGTFG: main
-- statement:
--   The FGTFG construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorsionFreeGenerators/FGTorsionFreeGenOf.lean#L34-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorsionFreeGenerators/FGTorsionFreeGenOf.lean#L34-L64

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_FGTorsionFreeGenOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FGTFG
open Module

theorem PI.FGTFG.main (hS : SplitStep) (h1 : RankOneStep) (R : Type) [CommRing R] [IsDedekindDomain R] :
    ∀ n : ℕ, ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [NoZeroSMulDivisors R M], finrank R M = n →
      ∃ s : Finset M, s.card ≤ n + 1 ∧ Submodule.span R (s : Set M) = ⊤ := by sorry
