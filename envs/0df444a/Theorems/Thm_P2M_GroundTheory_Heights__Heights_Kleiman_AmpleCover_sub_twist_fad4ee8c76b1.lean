-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_twist_fad4ee8c76b1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_twist_fad4ee8c76b1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:58.147121+00:00
-- url     : https://prove2.me/theorems/ab995f19-4c05-4d65-98f2-917f35c0cc08
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Cover sub twist fad4ee8c76b1: P2 M Ground Theory Heights  Heights Kleiman Ample Cover sub twist fad4ee8c76b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Cover sub twist fad4ee8c76b1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Cover sub twist fad4ee8c76b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleCover.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleCover.lean#L16-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleCover
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_twist_fad4ee8c76b1 (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleCover».«sub_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_twist_fad4ee8c76b1
