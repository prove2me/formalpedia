-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_interNum_fin_congr_f8923f4ce7c1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_interNum_fin_congr_f8923f4ce7c1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:14.305429+00:00
-- url     : https://prove2.me/theorems/1d6a0865-e224-53f5-b997-5a719540fe02
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop inter Num fin congr f8923f4ce7c1: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop inter Num fin congr f8923f4ce7c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop inter Num fin congr f8923f4ce7c1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop inter Num fin congr f8923f4ce7c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDrop.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDrop.lean#L100-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDrop
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
open Filter
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_interNum_fin_congr_f8923f4ce7c1 {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {a a' : ℕ} (h : a = a') (pp : Ideal (Poly S N)) (F : SubSystem S x Ω) :
    interNum pp (fun _ : Fin a => F) = interNum pp (fun _ : Fin a' => F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«interNum_fin_congr» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_interNum_fin_congr_f8923f4ce7c1
