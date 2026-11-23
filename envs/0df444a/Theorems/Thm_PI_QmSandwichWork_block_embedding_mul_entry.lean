-- Prove2me | Theorems.Thm_PI_QmSandwichWork_block_embedding_mul_entry
-- name    : PI.QmSandwichWork.block_embedding_mul_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:53.975108+00:00
-- url     : https://prove2.me/theorems/0e023a22-406e-4805-b136-7e8ab4c78955
-- title:
--   Qm Sandwich Work: block embedding mul entry
-- statement:
--   The Qm Sandwich Work construction uses the block embedding mul entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EntrywiseSandwichCommute/BlockEmbeddingMulEntrySwap.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EntrywiseSandwichCommute/BlockEmbeddingMulEntrySwap.lean#L36-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_RttRelation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EntrywiseSandwichCommute_BlockEmbeddingMulEntrySwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmSandwichWork
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P.W
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem PI.QmSandwichWork.block_embedding_mul_entry (M N : Matrix (Fin 2) (Fin 2) A) : (E1 M * E2 N) (0, 0) (0, 0) = M 0 0 * N 0 0 := by sorry
