-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventually_sub_ac7cc952d78a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventually_sub_ac7cc952d78a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:34.147039+00:00
-- url     : https://prove2.me/theorems/5e2cabb0-85f2-4ad7-ab76-060def6bce58
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eventually sub ac7cc952d78a: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eventually sub ac7cc9
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eventually sub ac7cc952d78a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eventually sub ac7cc952d78a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L58-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
variable {K : Type*}
variable [DecidableEq K]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventually_sub_ac7cc952d78a {P : (K → ℤ) → Prop} (h : ∀ᶠ m in atTop, P m) (x : K → ℤ) :
    ∀ᶠ m in atTop, P (m - x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«eventually_sub» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventually_sub_ac7cc952d78a
