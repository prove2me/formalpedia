-- Prove2me | Theorems.Thm_PI_SqPair_LCP_finiteAdeleIdempotentOfF_mul_self
-- name    : PI.SqPair.LCP.finiteAdeleIdempotentOfF_mul_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:43.066535+00:00
-- url     : https://prove2.me/theorems/48a8f738-8b35-406d-8851-a36285f2c7dc
-- title:
--   LCP: finite Adele Idempotent Of F mul self
-- statement:
--   The LCP construction uses the finite Adele Idempotent Of F mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L14-L15

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

theorem PI.SqPair.LCP.finiteAdeleIdempotentOfF_mul_self : (e0 : Matrix (Fin 2) (Fin 2) R) * e0 = e0 := by sorry
