-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_pow
-- name    : PI.SqPair.LocCartanPairW.cmp_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:01.913724+00:00
-- url     : https://prove2.me/theorems/065e1850-8255-40e6-b169-9fa23fac09d5
-- title:
--   Loc Cartan Pair W: cmp pow
-- statement:
--   The Loc Cartan Pair W construction uses the cmp pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L183-L186

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
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
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)

theorem PI.SqPair.LocCartanPairW.cmp_pow (ϖ : R) (hϖ : σ ϖ = ϖ) (m a k : ℕ) (hk : m + a = k) :
    σ (ϖ ^ m) * (ϖ ^ m * ϖ ^ (2 * a)) = ϖ ^ (2 * k) := by sorry
