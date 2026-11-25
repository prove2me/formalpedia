-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_scl_weight
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.scl_weight
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:55.336951+00:00
-- url     : https://prove2.me/theorems/5ad7e6fa-e2ac-5136-825a-fcc1bef2a1c8
-- title:
--   OSAux: scl weight
-- statement:
--   The OSAux construction uses the scl weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqNonneg.lean#L231-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqNonneg.lean#L231-L317

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.scl_weight (hS : SUB) {δ γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hγ0 : 0 < γ) (hγ : γ ≤ δ / 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ {p m : ℕ} (η η' : Fin (p + 1) → ℂ) (ζ : Fin m → ℂ) (x : Xp (p + 1) m),
      ∫⁻ τ in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4)) ≤
        ENNReal.ofReal C * (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) := by sorry
