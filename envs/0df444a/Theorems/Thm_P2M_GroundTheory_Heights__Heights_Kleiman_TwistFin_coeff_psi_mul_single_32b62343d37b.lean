-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_coeff_psi_mul_single_32b62343d37b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_coeff_psi_mul_single_32b62343d37b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:45.858368+00:00
-- url     : https://prove2.me/theorems/4e5d71b4-34d9-56ba-bc20-df8cb9319e5a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin coeff psi mul single 32b62343d37b: P2 M Ground Theory Heights  Heights Kleiman Twist Fin coeff psi mul single 32b62343d37b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin coeff psi mul single 32b62343d37b construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin coeff psi mul single 32b62343d37b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L201-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L201-L212

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
variable (M0 : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_coeff_psi_mul_single_32b62343d37b (c : Sy S r) (b' b : ℕ) (s' : Ω) :
    (psi η S c * single ((0 : ℤ), (b' : ℤ)) s').coeff ((0 : ℤ), (b : ℤ)) =
      ∑ d ∈ Finset.range (c.totalDegree + 1),
        if d + b' = b then aeval η (homogeneousComponent d c) * s' else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«coeff_psi_mul_single» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_coeff_psi_mul_single_32b62343d37b
