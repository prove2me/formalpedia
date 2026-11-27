-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FieldNumbers_blockIncl_injective_5f0b79acc28b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FieldNumbers_blockIncl_injective_5f0b79acc28b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:23:18.64082+00:00
-- url     : https://prove2.me/theorems/b36bcd57-d60f-51dc-8398-8e4c4620ac7d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Field Numbers block Incl injective 5f0b79acc28b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Field Numbers blo
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Field Numbers block Incl injective 5f0b79acc28b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Field Numbers block Incl injective 5f0b79acc28b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PfContractedHypothesesExample.lean#L264-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PfContractedHypothesesExample.lean#L264-L267

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u u' v v' w

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FieldNumbers_blockIncl_injective_5f0b79acc28b {F : Type u} [Field F] {K : Type v} {L : Type v'} {ι : K → Type w}
    (ι₂ : L → Type w) : Function.Injective (blockIncl (F := F) (ι := ι) ι₂) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FieldNumbers».«blockIncl_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FieldNumbers_blockIncl_injective_5f0b79acc28b
