-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_pre_21c24d8dc7c8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_pre_21c24d8dc7c8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:40.312153+00:00
-- url     : https://prove2.me/theorems/c2eebbd2-3944-5448-9bcb-9c6610cdb538
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin chart pre 21c24d8dc7c8: P2 M Ground Theory Heights  Heights Kleiman Twist Fin chart pre 21c24d8dc7c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin chart pre 21c24d8dc7c8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin chart pre 21c24d8dc7c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L174-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L174-L199

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
variable {n0 d0 g0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_pre_21c24d8dc7c8 (G B : LineBundle S x)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)
    (hG : ∀ I, M0.tilde 0 I = G.sub I)
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) (b : ℕ) {ω : Ω}
    (hω : ω ∈ (G.twist (B.pow b)).sub (toChart x I hI)) :
    ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) ω) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«chart_pre» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_pre_21c24d8dc7c8
