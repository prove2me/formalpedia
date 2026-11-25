-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_map_mem_map_31a912463f73
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_map_mem_map_31a912463f73
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:57.391475+00:00
-- url     : https://prove2.me/theorems/f9540d55-be01-4cd2-83f0-f37887dba0b7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem of map mem map 31a912463f73: P2 M Ground Theory Heights  Heights Kleiman mem of map mem map 31a912463f73
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem of map mem map 31a912463f73 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem of map mem map 31a912463f73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreSectionsFlat.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreSectionsFlat.lean#L28-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDedekindFibreRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
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
open scoped Pointwise
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_map_mem_map_31a912463f73 {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} {qq : Ideal (Poly S N)} (hq : qq.IsPrime)
    (hconst : ∀ s : S, (C s : Poly S N) ∈ qq → s = 0) {p : Poly S N}
    (hp : MvPolynomial.map (algebraMap S F) p ∈ qq.map (MvPolynomial.map (algebraMap S F))) : p ∈ qq := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_of_map_mem_map» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_map_mem_map_31a912463f73
