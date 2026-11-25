-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_gram_core
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_gram_core
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:50:10.882212+00:00
-- url     : https://prove2.me/theorems/9c2a5977-cf7b-4993-a8d3-65e984a739dc
-- title:
--   Step A: ea gram core
-- statement:
--   The Step A construction uses the ea gram core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/StarLastDotLast.lean#L32-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/StarLastDotLast.lean#L32-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_gram_core {k r' m : ℕ} {κ : Mat k (1 + r')} (hκ : κᴴ * κ = 1) {D : ℝ} (hD : D ≠ 0)
    (W : Fin (m + 1) → Fin (2 * (1 + r') + k + 1) → ℂ) (U : Fin m → Fin (2 * r' + k + 1) → ℂ) (β : Fin m → ℂ)
    (h0 : W 0 = κ *ᵥ ((D : ℂ) • es0 k r'))
    (hs : ∀ i, W i.succ = κ *ᵥ (liftVec k 1 r' (U i) + β i • es0 k r')) :
    Matrix.det (Matrix.of fun a b => star (W a) ⬝ᵥ W b) =
      (D : ℂ) ^ 2 * Matrix.det (Matrix.of fun a b => star (U a) ⬝ᵥ U b) := by sorry
