-- Prove2me | Theorems.Thm_P2M_PI_MirabolicIndex__card_nonzero_92fe098ea246
-- name    : P2M_PI_MirabolicIndex__card_nonzero_92fe098ea246
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:53.505409+00:00
-- url     : https://prove2.me/theorems/4e2165a8-ea0d-4e83-8dbc-3bb4d9c6bced
-- title:
--   P2 M PI Mirabolic Index  card nonzero 92fe098ea246: P2 M PI Mirabolic Index  card nonzero 92fe098ea246
-- statement:
--   The P2 M PI Mirabolic Index  card nonzero 92fe098ea246 construction uses the P2 M PI Mirabolic Index  card nonzero 92fe098ea246 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L119-L124

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

theorem P2M_PI_MirabolicIndex__card_nonzero_92fe098ea246 (n : ℕ) :
    Nat.card {v : Fin (n + 1) → k // v ≠ 0} = Fintype.card k ^ (n + 1) - 1 := by sorry

alias «PI».«MirabolicIndex₂».«card_nonzero» := P2M_PI_MirabolicIndex__card_nonzero_92fe098ea246
