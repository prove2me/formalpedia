-- Prove2me | Theorems.Thm_PI_LocCartanPair_hypJ_det
-- name    : PI.LocCartanPair.hypJ_det
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:01.724805+00:00
-- url     : https://prove2.me/theorems/5be6d14f-a806-5947-9b4b-9e3e2405a8b7
-- title:
--   Loc Cartan Pair: hyp J det
-- statement:
--   The Loc Cartan Pair construction uses the hyp J det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean#L70-L72

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R]
variable (κ : Type) [Fintype κ] [DecidableEq κ]

theorem PI.LocCartanPair.hypJ_det : IsUnit (hypJ κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R).det := by sorry
