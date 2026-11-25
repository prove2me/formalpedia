-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_eq_mixedDiff_6117ca062b3f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_eq_mixedDiff_6117ca062b3f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:41.313487+00:00
-- url     : https://prove2.me/theorems/145841af-7468-4429-ab15-337a8776d7f6
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff eq mixed Diff 6117ca062b3f: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff eq mixed D
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff eq mixed Diff 6117ca062b3f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff eq mixed Diff 6117ca062b3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L145-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L145-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
variable {K : Type} [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_eq_mixedDiff_6117ca062b3f (f : (K → ℤ) → ℤ) (c : ℕ) (L : List K) (t : K → ℕ) :
    listDiff L (fun t => (f (fun k => (c : ℤ) + t k) : ℚ)) t =
      (((L.map fun k => (Pi.single k 1 : K → ℤ)).foldr diffStep f)
        (fun k => (c : ℤ) + t k + L.count k) : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolynomial».«listDiff_eq_mixedDiff» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_eq_mixedDiff_6117ca062b3f
