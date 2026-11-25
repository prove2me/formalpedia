-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_finite_of_pow_mem_d0bf03a092a4
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_finite_of_pow_mem_d0bf03a092a4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:56.288612+00:00
-- url     : https://prove2.me/theorems/400b5136-0173-40c6-8482-c695884b6885
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite finite of pow mem d0bf03a092a4: P2 M Ground Theory Heights  Heights Vertical Sec BFinite finite of pow mem d0bf03a092a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite finite of pow mem d0bf03a092a4 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite finite of pow mem d0bf03a092a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L65-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L65-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_finite_of_pow_mem_d0bf03a092a4 {R : Type*} [CommRing R] {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) R))
    (M : Fin n → ℕ) (q : Fin n → MvPolynomial (Fin n) R) (hq : ∀ j, (q j).totalDegree < M j)
    (hQ : ∀ j, X j ^ M j - q j ∈ Q) : Module.Finite R (MvPolynomial (Fin n) R ⧸ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«finite_of_pow_mem» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_finite_of_pow_mem_d0bf03a092a4
