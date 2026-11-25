-- Prove2me | Theorems.Thm_PI_SqPairLocal_exists_den
-- name    : PI.SqPairLocal.exists_den
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:25:10.017513+00:00
-- url     : https://prove2.me/theorems/b8e45e2d-3765-492e-96c1-25bedcaa808e
-- title:
--   Sq Pair Local: exists den
-- statement:
--   The Sq Pair Local construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsDenFg.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsDenFg.lean#L101-L104

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

theorem PI.SqPairLocal.exists_den (L'' : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ L'' := by sorry
