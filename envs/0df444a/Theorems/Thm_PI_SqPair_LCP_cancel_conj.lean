-- Prove2me | Theorems.Thm_PI_SqPair_LCP_cancel_conj
-- name    : PI.SqPair.LCP.cancel_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:08.533496+00:00
-- url     : https://prove2.me/theorems/d5ea5b63-0388-51c6-9625-83d713bfb804
-- title:
--   LCP: cancel conj
-- statement:
--   The LCP construction uses the cancel conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L28-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R]

theorem PI.SqPair.LCP.cancel_conj {ι : Type} [Fintype ι] [DecidableEq ι] {u X Y : Matrix ι ι R}
    (hu : IsUnit u.det) (h : uᴴ * X * u = uᴴ * Y * u) : X = Y := by sorry
