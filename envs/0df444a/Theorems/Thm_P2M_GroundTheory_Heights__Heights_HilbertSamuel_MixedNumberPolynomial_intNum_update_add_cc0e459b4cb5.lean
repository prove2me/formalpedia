-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_update_add_cc0e459b4cb5
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_update_add_cc0e459b4cb5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:32.209824+00:00
-- url     : https://prove2.me/theorems/4fdc8305-6549-4452-81b3-f940920426c0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial int Num update add cc0e459b4cb5: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial int Num update ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial int Num update add cc0e459b4cb5 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial int Num update add cc0e459b4cb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L77-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L77-L107

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_update_add_cc0e459b4cb5 (F : Type*) [Field F] {ι : K → Type*} (q : Ideal (MRing ι F)) {d : ℕ}
    (hex : ∀ bs : Fin d → K → ℤ, ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn q) m = c)
    (bs : Fin d → K → ℤ) (j : Fin d) (x y : K → ℤ) :
    intNum F q (Function.update bs j (x + y)) =
      intNum F q (Function.update bs j x) + intNum F q (Function.update bs j y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«intNum_update_add» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_update_add_cc0e459b4cb5
