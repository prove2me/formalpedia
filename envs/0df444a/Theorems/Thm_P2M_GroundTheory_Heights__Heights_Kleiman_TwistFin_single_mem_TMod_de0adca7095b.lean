-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_TMod_de0adca7095b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_TMod_de0adca7095b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:20.501695+00:00
-- url     : https://prove2.me/theorems/ee55e17a-a777-5de2-8e19-032068ce23aa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin single mem TMod de0adca7095b: P2 M Ground Theory Heights  Heights Kleiman Twist Fin single mem TMod de0adca7095b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin single mem TMod de0adca7095b construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin single mem TMod de0adca7095b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L28-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L28-L58

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_TMod_de0adca7095b (M0 : FinGradedSub (S := S) (x := x) Ω)
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    {a : ℤ} {m : Ω} (hm : m ∈ M0.piece a) :
    (toA x η).symm (single (a, (0 : ℤ)) m) ∈ TMod x η S n0 d0 g0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«single_mem_TMod» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_TMod_de0adca7095b
