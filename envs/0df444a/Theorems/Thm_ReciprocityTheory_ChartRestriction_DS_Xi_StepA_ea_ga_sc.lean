-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_ga_sc
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_ga_sc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:08.693806+00:00
-- url     : https://prove2.me/theorems/63701032-4ffa-5e11-96b7-4338553dc5f9
-- title:
--   Step A: ea ga sc
-- statement:
--   The Step A construction uses the ea ga sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/StarLastDotLast.lean#L82-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/StarLastDotLast.lean#L82-L96

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_ga_sc {k r' : ℕ} {κ : Mat k (1 + r')} (hκ : κᴴ * κ = 1) {D : ℝ} (hD : D ≠ 0)
    (Y : Fin (1 + r' + 1) → Fin (2 * (1 + r') + k + 1) → ℂ) (U : Fin (r' + 1) → Fin (2 * r' + k + 1) → ℂ)
    (β : Fin (r' + 1) → ℂ) (h0 : Y 0 = κ *ᵥ ((D : ℂ) • es0 k r'))
    (hs : ∀ b, Y (sc r' b) = κ *ᵥ (liftVec k 1 r' (U b) + β b • es0 k r')) (l : Fin (r' + 1)) :
    Ga k (1 + r') (sc r' l) Y = D ^ 2 * Ga k r' l U := by sorry
