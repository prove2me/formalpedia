-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_curveClosure_d5266bbc86d1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_curveClosure_d5266bbc86d1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:21.762502+00:00
-- url     : https://prove2.me/theorems/7697c9b0-b057-481b-86c4-e3ed11db1126
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman curve Closure d5266bbc86d1: P2 M Ground Theory Heights  Heights Kleiman curve Closure d5266bbc86d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman curve Closure d5266bbc86d1 construction uses the P2 M Ground Theory Heights  Heights Kleiman curve Closure d5266bbc86d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefGeneric.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefGeneric.lean#L12-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsNefGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefGeneric
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
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_curveClosure_d5266bbc86d1 {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} (pp : Ideal (Poly F N)) [pp.IsPrime] :
    (∀ s : S, (C s : Poly S N) ∈ pp.comap (MvPolynomial.map (algebraMap S F)) → s = 0) ∧
      (pp.comap (MvPolynomial.map (algebraMap S F))).map (MvPolynomial.map (algebraMap S F)) = pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«curveClosure» := P2M_GroundTheory_Heights__Heights_Kleiman_curveClosure_d5266bbc86d1
