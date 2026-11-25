-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_gen_pre_cba970ff5a87
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_gen_pre_cba970ff5a87
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:29.256418+00:00
-- url     : https://prove2.me/theorems/84413049-1f45-4e1b-ab1b-a173a8a9fd59
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin gen pre cba970ff5a87: P2 M Ground Theory Heights  Heights Kleiman Twist Fin gen pre cba970ff5a87
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin gen pre cba970ff5a87 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin gen pre cba970ff5a87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L139-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L139-L170

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_gen_pre_cba970ff5a87
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) (b : ℕ) {ω : Ω}
    (hω : ω ∈ genSet x η S M0 (toChart x I hI) b) :
    ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) ω) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«gen_pre» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_gen_pre_cba970ff5a87
