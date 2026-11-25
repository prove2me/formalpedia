-- Prove2me | Theorems.Thm_PI_HermitianEmbeddingSlice_dd_star
-- name    : PI.HermitianEmbeddingSlice.dd_star
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:06:14.644957+00:00
-- url     : https://prove2.me/theorems/60618b8f-00f4-593e-b8eb-0122b1d1d4e7
-- title:
--   Hermitian Embedding Slice: dd star
-- statement:
--   The Hermitian Embedding Slice construction uses the dd star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/WbPartBvecEI.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/WbPartBvecEI.lean#L25-L27

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

theorem PI.HermitianEmbeddingSlice.dd_star (j : Fin (k + 1)) : star (dd k j) = dd k j := by sorry
