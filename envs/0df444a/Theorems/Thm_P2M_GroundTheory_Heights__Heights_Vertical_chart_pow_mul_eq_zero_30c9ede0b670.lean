-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_chart_pow_mul_eq_zero_30c9ede0b670
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_chart_pow_mul_eq_zero_30c9ede0b670
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:44:27.075962+00:00
-- url     : https://prove2.me/theorems/2aca4ae5-3e4a-4817-a928-f2b68dabd49d
-- title:
--   P2 M Ground Theory Heights  Heights Vertical chart pow mul eq zero 30c9ede0b670: P2 M Ground Theory Heights  Heights Vertical chart pow mul eq zero 30c9ede0b670
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical chart pow mul eq zero 30c9ede0b670 construction uses the P2 M Ground Theory Heights  Heights Vertical chart pow mul eq zero 30c9ede0b670 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L280-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L280-L321

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
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
variable {D : Type*} [CommRing D] {n : ℕ}
variable (e : ℕ) (R : Type*) [CommRing R] [Algebra (MvPolynomial (Par e n) D) R]
variable (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (S : Submonoid (MvPolynomial (Par e n) D))

theorem P2M_GroundTheory_Heights__Heights_Vertical_chart_pow_mul_eq_zero_30c9ede0b670 [IsDomain D] [Q.IsPrime] [IsLocalization S R]
    (hQ : ∀ c : D, C c ∈ Q → c = 0) (c : D) (hc : c ≠ 0)
    (b : SecAlg (chartModel e R Q) (chartPar D e R))
    (hb : algebraMap R _ (algebraMap (MvPolynomial (Par e n) D) R (C c)) * b = 0) :
    ∃ N : ℕ, secCoord (chartModel e R Q) (chartPar D e R) j ^ N * b = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«chart_pow_mul_eq_zero» := P2M_GroundTheory_Heights__Heights_Vertical_chart_pow_mul_eq_zero_30c9ede0b670
