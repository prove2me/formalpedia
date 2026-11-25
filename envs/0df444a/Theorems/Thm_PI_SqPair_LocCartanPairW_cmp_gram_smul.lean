-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_gram_smul
-- name    : PI.SqPair.LocCartanPairW.cmp_gram_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:16.49928+00:00
-- url     : https://prove2.me/theorems/60498c00-6b4c-468d-8b1e-c48106f6e822
-- title:
--   Loc Cartan Pair W: cmp gram smul
-- statement:
--   The Loc Cartan Pair W construction uses the cmp gram smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L23-L32

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

theorem PI.SqPair.LocCartanPairW.cmp_gram_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι R) (a b : R) (v w : ι → R) :
    (fun i => σ ((a • v) i)) ⬝ᵥ (A *ᵥ (b • w)) = σ a * b * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by sorry
