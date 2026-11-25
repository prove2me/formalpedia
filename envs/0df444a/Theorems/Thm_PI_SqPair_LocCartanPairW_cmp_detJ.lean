-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_detJ
-- name    : PI.SqPair.LocCartanPairW.cmp_detJ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:38.123126+00:00
-- url     : https://prove2.me/theorems/87f0d214-93d7-5c9a-934e-10f8b3408daf
-- title:
--   Loc Cartan Pair W: cmp det J
-- statement:
--   The Loc Cartan Pair W construction uses the cmp det J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L49-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
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

theorem PI.SqPair.LocCartanPairW.cmp_detJ [Nontrivial R] : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by sorry
