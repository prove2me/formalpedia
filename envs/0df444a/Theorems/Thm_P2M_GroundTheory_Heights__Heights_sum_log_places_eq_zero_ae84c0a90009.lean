-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_log_places_eq_zero_ae84c0a90009
-- name    : P2M_GroundTheory_Heights__Heights_sum_log_places_eq_zero_ae84c0a90009
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:40.86396+00:00
-- url     : https://prove2.me/theorems/37f8144b-11fa-4593-aff3-3cbd8da0077d
-- title:
--   P2 M Ground Theory Heights  Heights sum log places eq zero ae84c0a90009: P2 M Ground Theory Heights  Heights sum log places eq zero ae84c0a90009
-- statement:
--   The P2 M Ground Theory Heights  Heights sum log places eq zero ae84c0a90009 construction uses the P2 M Ground Theory Heights  Heights sum log places eq zero ae84c0a90009 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L125-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L125-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_sum_log_places_eq_zero_ae84c0a90009 {t : K} (ht : t ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v t)) + ∑ σ : K →+* ℂ, Real.log ‖σ t‖ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_log_places_eq_zero» := P2M_GroundTheory_Heights__Heights_sum_log_places_eq_zero_ae84c0a90009
