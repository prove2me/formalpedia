-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:26.255115+00:00
-- url     : https://prove2.me/theorems/e4027db0-638c-5775-9a70-1ce3efb0eca3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mono Prod is Homogeneous 4a7cd1fe755c: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mono Prod is Homogeneous 4a7cd1fe755c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mono Prod is Homogeneous 4a7cd1fe755c construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mono Prod is Homogeneous 4a7cd1fe755c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L44-L48

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c (T : Finset (Fin (N + 1))) :
    (monoProd (S := S) T).IsHomogeneous T.card := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«monoProd_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c
