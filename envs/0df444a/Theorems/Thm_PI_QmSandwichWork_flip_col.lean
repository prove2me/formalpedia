-- Prove2me | Theorems.Thm_PI_QmSandwichWork_flip_col
-- name    : PI.QmSandwichWork.flip_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:08.16685+00:00
-- url     : https://prove2.me/theorems/a15d76b6-3472-467b-898b-9f7d0a8d0287
-- title:
--   Qm Sandwich Work: flip col
-- statement:
--   The Qm Sandwich Work construction uses the flip col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EntrywiseSandwichCommute/BlockEmbeddingMulEntrySwap.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EntrywiseSandwichCommute/BlockEmbeddingMulEntrySwap.lean#L30-L34

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

theorem PI.QmSandwichWork.flip_col (D : ℂ) (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) :
    (K * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) (0, 0) (0, 0) =
      algebraMap ℂ A (D - 1) * K (0, 0) (0, 0) := by sorry
