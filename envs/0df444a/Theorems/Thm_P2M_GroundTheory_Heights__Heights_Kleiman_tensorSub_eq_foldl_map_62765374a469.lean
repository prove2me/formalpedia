-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_foldl_map_62765374a469
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_foldl_map_62765374a469
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:11:13.568949+00:00
-- url     : https://prove2.me/theorems/e8abaf63-c8ef-4d0b-a199-70b8918e8268
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tensor Sub eq foldl map 62765374a469: P2 M Ground Theory Heights  Heights Kleiman tensor Sub eq foldl map 62765374a469
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tensor Sub eq foldl map 62765374a469 construction uses the P2 M Ground Theory Heights  Heights Kleiman tensor Sub eq foldl map 62765374a469 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
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
open MvPolynomial Filter
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_foldl_map_62765374a469 {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (((List.finRange n).filter (· ∈ T)).map L).foldl
      (fun F Q => F.twist Q) (twistSys S x 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«tensorSub_eq_foldl_map» := P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_foldl_map_62765374a469
