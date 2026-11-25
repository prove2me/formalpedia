-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_twist_sub_le_b74da22da760
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_twist_sub_le_b74da22da760
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:26.056751+00:00
-- url     : https://prove2.me/theorems/f4bdb87a-e4bd-515e-bf4a-f7e6ba8c3032
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin twist sub le b74da22da760: P2 M Ground Theory Heights  Heights Kleiman Twist Fin twist sub le b74da22da760
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin twist sub le b74da22da760 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin twist sub le b74da22da760 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L114-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L114-L136

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_twist_sub_le_b74da22da760 (G B : LineBundle S x)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)
    (hG : ∀ I, M0.tilde 0 I = G.sub I) (I : Chart x) (b : ℕ) :
    ∀ ω ∈ (G.twist (B.pow b)).sub I, ω ∈ Submodule.span S (genSet x η S M0 I b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«twist_sub_le» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_twist_sub_le_b74da22da760
