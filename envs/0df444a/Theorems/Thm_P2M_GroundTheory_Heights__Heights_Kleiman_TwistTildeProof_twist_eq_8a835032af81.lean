-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistTildeProof_twist_eq_8a835032af81
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistTildeProof_twist_eq_8a835032af81
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:11.172199+00:00
-- url     : https://prove2.me/theorems/ddd19711-91c3-40d0-b991-05d8a63cd624
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Tilde Proof twist eq 8a835032af81: P2 M Ground Theory Heights  Heights Kleiman Twist Tilde Proof twist eq 8a835032af81
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Tilde Proof twist eq 8a835032af81 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Tilde Proof twist eq 8a835032af81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistTilde.lean#L66-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistTilde.lean#L66-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistTildeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistTilde
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.TwistTildeProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistTildeProof_twist_eq_8a835032af81 (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω)
    (I : Chart x) : ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = (prod M Q).tilde 0 I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistTildeProof».«twist_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistTildeProof_twist_eq_8a835032af81
