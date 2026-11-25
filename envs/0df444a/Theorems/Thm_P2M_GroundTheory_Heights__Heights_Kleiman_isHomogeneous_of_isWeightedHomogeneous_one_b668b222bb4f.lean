-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isHomogeneous_of_isWeightedHomogeneous_one_b668b222bb4f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isHomogeneous_of_isWeightedHomogeneous_one_b668b222bb4f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:48.038911+00:00
-- url     : https://prove2.me/theorems/8990cc3c-c059-5ef8-b3ef-d3a55b5169e5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Homogeneous of is Weighted Homogeneous one b668b222bb4f: P2 M Ground Theory Heights  Heights Kleiman is Homogeneous of is Weighted Homogeneous one b668b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Homogeneous of is Weighted Homogeneous one b668b222bb4f construction uses the P2 M Ground Theory Heights  Heights Kleiman is Homogeneous of is Weighted Homogeneous one b668b222bb4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/QuotGraded.lean#L107-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/QuotGraded.lean#L107-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
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
open MvPolynomial DirectSum
noncomputable section
universe u
variable {S : Type u} [CommRing S] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isHomogeneous_of_isWeightedHomogeneous_one_b668b222bb4f {f : Poly S N} {n : ℕ}
    (hf : IsWeightedHomogeneous (fun _ => (1 : ℤ)) f (n : ℤ)) : f.IsHomogeneous n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isHomogeneous_of_isWeightedHomogeneous_one» := P2M_GroundTheory_Heights__Heights_Kleiman_isHomogeneous_of_isWeightedHomogeneous_one_b668b222bb4f
