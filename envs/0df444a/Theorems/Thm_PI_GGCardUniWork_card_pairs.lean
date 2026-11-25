-- Prove2me | Theorems.Thm_PI_GGCardUniWork_card_pairs
-- name    : PI.GGCardUniWork.card_pairs
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:31:23.085424+00:00
-- url     : https://prove2.me/theorems/2a0df54c-b721-4cd7-9ed1-0e3a1cdafc7b
-- title:
--   GGCard Uni Work: card pairs
-- statement:
--   The GGCard Uni Work construction uses the card pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCardinality/UniMatUpper.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCardinality/UniMatUpper.lean#L56-L64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCardinality_UniMatUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGCardUniWork
open Finset Matrix Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem PI.GGCardUniWork.card_pairs (k : ℕ) : Fintype.card (Pairs k) = k * (k - 1) / 2 := by sorry
