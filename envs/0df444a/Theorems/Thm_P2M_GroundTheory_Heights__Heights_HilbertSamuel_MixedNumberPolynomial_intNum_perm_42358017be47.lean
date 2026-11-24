-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_perm_42358017be47
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_perm_42358017be47
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:35.201389+00:00
-- url     : https://prove2.me/theorems/cc16f55b-bf54-48cd-8ca7-d739471d01ad
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial int Num perm 42358017be47: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial int Num perm 42358017be
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial int Num perm 42358017be47 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial int Num perm 42358017be47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L43-L46

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_perm_42358017be47 (F : Type*) [Field F] {ι : K → Type*} (q : Ideal (MRing ι F)) {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ) : intNum F q (bs ∘ σ) = intNum F q bs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«intNum_perm» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_perm_42358017be47
