-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:28.689777+00:00
-- url     : https://prove2.me/theorems/86448828-83ae-5a80-af12-b4a6e10ca34f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen aeval mono Prod 6aa38ad48f99: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen aeval mono Prod 6aa38ad48f99
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen aeval mono Prod 6aa38ad48f99 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen aeval mono Prod 6aa38ad48f99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L54-L56

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99 (T : Finset (Fin (N + 1))) :
    aeval x (monoProd (S := S) T) = ∏ i ∈ T, x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«aeval_monoProd» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99
