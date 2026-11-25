-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_mono_a1444dbbcbc5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_mono_a1444dbbcbc5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:12:09.134964+00:00
-- url     : https://prove2.me/theorems/fb2f2f93-46e7-5d23-a8ea-4bf540e8e181
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist sub mono a1444dbbcbc5: P2 M Ground Theory Heights  Heights Kleiman twist sub mono a1444dbbcbc5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist sub mono a1444dbbcbc5 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist sub mono a1444dbbcbc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotDevissage.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotDevissage.lean#L23-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotDevissage
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_mono_a1444dbbcbc5 {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) (Q : SubSystem S x Ω)
    (I : Chart x) : (F.twist Q).sub I ≤ (G.twist Q).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_sub_mono» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_mono_a1444dbbcbc5
