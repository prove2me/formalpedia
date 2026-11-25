-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_d_one_d_zero_2a2432191898
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_d_one_d_zero_2a2432191898
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:31.51281+00:00
-- url     : https://prove2.me/theorems/ff468c1c-211b-44c7-ad44-a4139d7cbdba
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System d one d zero 2a2432191898: P2 M Ground Theory Heights  Heights Kleiman Sub System d one d zero 2a2432191898
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System d one d zero 2a2432191898 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System d one d zero 2a2432191898 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L87-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
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
open GroundTheory.Heights₂.Heights.Kleiman.SubSystem
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_d_one_d_zero_2a2432191898 (F : SubSystem S x E) (w : Cech.Cochain (fun I => F.sub I) 0) :
    Cech.d (fun I => F.sub I) F.res 1 (Cech.d (fun I => F.sub I) F.res 0 w) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«d_one_d_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_d_one_d_zero_2a2432191898
