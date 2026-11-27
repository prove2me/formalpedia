-- Prove2me | Theorems.Thm_PI_HermitianEmbeddingSlice_alg2
-- name    : PI.HermitianEmbeddingSlice.alg2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:44.486717+00:00
-- url     : https://prove2.me/theorems/6a483cc1-391b-40a7-a678-29922d89708f
-- title:
--   Hermitian Embedding Slice: alg2
-- statement:
--   The Hermitian Embedding Slice construction uses the alg2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/StarSingleOne.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/StarSingleOne.lean#L16-L29

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

theorem PI.HermitianEmbeddingSlice.alg2 (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (zb : Fin (k + 1) → ℂ) (j : Fin (k + 1)) :
    dd k j * star (star zb ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))) = ((Hb k * μᴴ * Hb k) *ᵥ zb) j := by sorry
