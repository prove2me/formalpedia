-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_encard_pow_eq_of_ne_zero_dca1fadb3310
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_encard_pow_eq_of_ne_zero_dca1fadb3310
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:33.429107+00:00
-- url     : https://prove2.me/theorems/d92e67c4-8681-45f8-a524-51f2f3035f68
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets encard pow eq of ne zero dca1fadb3310: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets e
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets encard pow eq of ne zero dca1fadb3310 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets encard pow eq of ne zero dca1fadb3310 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPowerUnitCount.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPowerUnitCount.lean#L12-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsPowerUnitCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPowerUnitCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology Matrix Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_encard_pow_eq_of_ne_zero_dca1fadb3310 {m : ℕ} (hm : m ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    {a : ℂ | a ^ m = t}.encard = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«encard_pow_eq_of_ne_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_encard_pow_eq_of_ne_zero_dca1fadb3310
