-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_exists_eventually_const_1a8f49af4e5a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_exists_eventually_const_1a8f49af4e5a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:39.103155+00:00
-- url     : https://prove2.me/theorems/14f5b64e-e4d2-486c-b9ef-e65ead4199d5
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial exists eventually const 1a8f49af4e5a: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial exists event
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial exists eventually const 1a8f49af4e5a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial exists eventually const 1a8f49af4e5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L239-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L239-L268

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_exists_eventually_const_1a8f49af4e5a (h : MultigradedHilbertPolynomial.Statement.{u}) (F : Type u)
    [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (q : Ideal (MRing ι F)) (d : ℕ) (hq : IsMultiProjPrime q)
    (hdim : ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞))
    (bs : Fin d → K → ℤ) : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn q) m = c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«exists_eventually_const» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_exists_eventually_const_1a8f49af4e5a
