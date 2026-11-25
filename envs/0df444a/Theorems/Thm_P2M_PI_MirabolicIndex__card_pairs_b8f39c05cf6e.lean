-- Prove2me | Theorems.Thm_P2M_PI_MirabolicIndex__card_pairs_b8f39c05cf6e
-- name    : P2M_PI_MirabolicIndex__card_pairs_b8f39c05cf6e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:08.895027+00:00
-- url     : https://prove2.me/theorems/ef33b95b-a970-493b-81b1-72d792107ddb
-- title:
--   P2 M PI Mirabolic Index  card pairs b8f39c05cf6e: P2 M PI Mirabolic Index  card pairs b8f39c05cf6e
-- statement:
--   The P2 M PI Mirabolic Index  card pairs b8f39c05cf6e construction uses the P2 M PI Mirabolic Index  card pairs b8f39c05cf6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L201-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L201-L215

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MirabolicIndex₂
open Finset Matrix PI.MirabIndex
variable {k : Type} [Field k] [Fintype k]

theorem P2M_PI_MirabolicIndex__card_pairs_b8f39c05cf6e (n : ℕ) : Fintype.card (Pairs n) = (n + 1) * n / 2 := by sorry

alias «PI».«MirabolicIndex₂».«card_pairs» := P2M_PI_MirabolicIndex__card_pairs_b8f39c05cf6e
