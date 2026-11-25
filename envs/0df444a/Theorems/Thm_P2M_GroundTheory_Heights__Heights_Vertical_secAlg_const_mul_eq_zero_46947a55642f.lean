-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secAlg_const_mul_eq_zero_46947a55642f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_secAlg_const_mul_eq_zero_46947a55642f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:56.661295+00:00
-- url     : https://prove2.me/theorems/6bbab851-b726-4166-a5a4-41b7f27ba93b
-- title:
--   P2 M Ground Theory Heights  Heights Vertical sec Alg const mul eq zero 46947a55642f: P2 M Ground Theory Heights  Heights Vertical sec Alg const mul eq zero 46947a55642f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical sec Alg const mul eq zero 46947a55642f construction uses the P2 M Ground Theory Heights  Heights Vertical sec Alg const mul eq zero 46947a55642f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L325-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L325-L332

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_secAlg_const_mul_eq_zero_46947a55642f {D : Type*} [CommRing D] [IsDomain D] {n : ℕ} (e : ℕ) (R : Type*)
    [CommRing R] [Algebra (MvPolynomial (Par e n) D) R] (Q : Ideal (MvPolynomial (Fin n) D)) [Q.IsPrime]
    (S : Submonoid (MvPolynomial (Par e n) D)) [IsLocalization S R] (hQ : ∀ c : D, C c ∈ Q → c = 0)
    (QR : Ideal (MvPolynomial (Fin n) R)) (hQR : QR = chartModel e R Q) (y : Par e n → R)
    (hy : y = chartPar D e R) (c : D) (hc : c ≠ 0) (b : SecAlg QR y)
    (hb : algebraMap R _ (algebraMap (MvPolynomial (Par e n) D) R (C c)) * b = 0) : b = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«secAlg_const_mul_eq_zero» := P2M_GroundTheory_Heights__Heights_Vertical_secAlg_const_mul_eq_zero_46947a55642f
