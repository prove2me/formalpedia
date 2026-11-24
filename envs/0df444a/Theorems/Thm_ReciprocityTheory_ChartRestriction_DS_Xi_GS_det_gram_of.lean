-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_det_gram_of
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.det_gram_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:15:10.58111+00:00
-- url     : https://prove2.me/theorems/17d1985c-883d-4f25-b0b6-ab69573877e4
-- title:
--   GS: det gram of
-- statement:
--   The GS construction uses the det gram of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LinIndToLp.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LinIndToLp.lean#L60-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.det_gram_of (w u : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ)
    (hu : Orthonormal ℂ u) (hτ : τ.BlockTriangular id) (hw : ∀ a, w a = ∑ b, τ b a • u b) :
    (gram w).det = ((∏ j, ‖τ j j‖ ^ 2 : ℝ) : ℂ) := by sorry
