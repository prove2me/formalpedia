-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_tensorProd_powBundle_7fe273c34225
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_tensorProd_powBundle_7fe273c34225
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:54.649264+00:00
-- url     : https://prove2.me/theorems/4bcd9e8a-f5e1-4f8a-92e5-20f209029361
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen tensor Prod pow Bundle 7fe273c34225: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen tensor Prod pow Bundle 7fe273c34225
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen tensor Prod pow Bundle 7fe273c34225 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen tensor Prod pow Bundle 7fe273c34225 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L170-L173

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_tensorProd_powBundle_7fe273c34225 (Q H : LineBundle S x) (c : ℕ) :
    (Q.tensorProd (H.powBundle c)).toSubSystem = Q.toSubSystem.twist (H.toSubSystem.pow c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«tensorProd_powBundle» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_tensorProd_powBundle_7fe273c34225
