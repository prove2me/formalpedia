-- Prove2me | Theorems.Thm_PI_SqPairLocal_exists_den_fg
-- name    : PI.SqPairLocal.exists_den_fg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:25:18.668644+00:00
-- url     : https://prove2.me/theorems/a602eb6f-bdb0-4358-8c43-430f0fbc8943
-- title:
--   Sq Pair Local: exists den fg
-- statement:
--   The Sq Pair Local construction uses the exists den fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsDenFg.lean#L106-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsDenFg.lean#L106-L119

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Lemmata_GeneralBFactLeftBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsDenFg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem PI.SqPairLocal.exists_den_fg (L' L'' : Submodule (𝓞 E) (Fin N → E)) (hfg : L'.FG)
    (hsp : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ y ∈ L', d • y ∈ L'' := by sorry
