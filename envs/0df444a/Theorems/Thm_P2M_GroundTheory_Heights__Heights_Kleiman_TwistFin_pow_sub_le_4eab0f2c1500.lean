-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_pow_sub_le_4eab0f2c1500
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_pow_sub_le_4eab0f2c1500
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:14.288316+00:00
-- url     : https://prove2.me/theorems/c40df885-2372-5f63-8d92-bd87a021c5a6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin pow sub le 4eab0f2c1500: P2 M Ground Theory Heights  Heights Kleiman Twist Fin pow sub le 4eab0f2c1500
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin pow sub le 4eab0f2c1500 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin pow sub le 4eab0f2c1500 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L63-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L63-L87

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_pow_sub_le_4eab0f2c1500 (B : SubSystem S x Ω)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (I : Chart x) (b : ℕ) :
    (B.pow b).sub I ≤ Submodule.span (chartRing S x I)
      {z | ∃ h : MvPolynomial (Fin (r + 1)) S, h.IsHomogeneous b ∧ z = aeval η h} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«pow_sub_le» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_pow_sub_le_4eab0f2c1500
