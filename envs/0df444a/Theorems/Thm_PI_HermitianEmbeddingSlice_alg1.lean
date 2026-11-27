-- Prove2me | Theorems.Thm_PI_HermitianEmbeddingSlice_alg1
-- name    : PI.HermitianEmbeddingSlice.alg1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:37.6725+00:00
-- url     : https://prove2.me/theorems/0742c467-5b30-55a1-aa49-8cd5abdf2d0c
-- title:
--   Hermitian Embedding Slice: alg1
-- statement:
--   The Hermitian Embedding Slice construction uses the alg1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/StarSingleOne.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/StarSingleOne.lean#L13-L14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_WbPartBvecEI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_StarSingleOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HermitianEmbeddingSlice
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
variable {k r : ℕ}

theorem PI.HermitianEmbeddingSlice.alg1 (v : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : dd k j * (Hb k *ᵥ v) j = v j := by sorry
