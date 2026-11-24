-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_eq_3099f1494d11
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_eq_3099f1494d11
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:47.007991+00:00
-- url     : https://prove2.me/theorems/3e769306-dc9e-4a0a-988b-e4050439b739
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial mixed Diff eq 3099f1494d11: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial mixed Diff eq 3099f149
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial mixed Diff eq 3099f1494d11 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial mixed Diff eq 3099f1494d11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L35-L36

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_eq_3099f1494d11 {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff bs h = (List.ofFn bs).foldr gStep h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«mixedDiff_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_eq_3099f1494d11
