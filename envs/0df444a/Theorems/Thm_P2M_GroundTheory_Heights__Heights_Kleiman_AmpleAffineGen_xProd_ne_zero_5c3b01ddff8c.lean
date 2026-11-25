-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_xProd_ne_zero_5c3b01ddff8c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_xProd_ne_zero_5c3b01ddff8c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:18.261972+00:00
-- url     : https://prove2.me/theorems/e77faf05-2ed8-5d58-80f7-a184bda24727
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen x Prod ne zero 5c3b01ddff8c: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen x Prod ne zero 5c3b01ddff8c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen x Prod ne zero 5c3b01ddff8c construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen x Prod ne zero 5c3b01ddff8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L28-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_xProd_ne_zero_5c3b01ddff8c (I : Chart x) : xProd I ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«xProd_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_xProd_ne_zero_5c3b01ddff8c
