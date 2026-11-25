-- Prove2me | Theorems.Thm_PI_HermitianEmbeddingSlice_dd_sq
-- name    : PI.HermitianEmbeddingSlice.dd_sq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:06:36.593305+00:00
-- url     : https://prove2.me/theorems/3726112b-c18c-4d6d-b853-79efc17e7c55
-- title:
--   Hermitian Embedding Slice: dd sq
-- statement:
--   The Hermitian Embedding Slice construction uses the dd sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/WbPartBvecEI.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/WbPartBvecEI.lean#L21-L23

import Definitions.Def_Formalism_PeriodIntegrals_BordSlice
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_WbPartBvecEI
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

theorem PI.HermitianEmbeddingSlice.dd_sq (j : Fin (k + 1)) : dd k j * dd k j = 1 := by sorry
