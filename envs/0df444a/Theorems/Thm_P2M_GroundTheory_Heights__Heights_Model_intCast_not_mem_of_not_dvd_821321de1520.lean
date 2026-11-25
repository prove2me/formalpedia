-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_not_mem_of_not_dvd_821321de1520
-- name    : P2M_GroundTheory_Heights__Heights_Model_intCast_not_mem_of_not_dvd_821321de1520
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:14.383804+00:00
-- url     : https://prove2.me/theorems/7b8a0ba5-f5ff-4acb-b10b-157f22d6f9fb
-- title:
--   P2 M Ground Theory Heights  Heights Model int Cast not mem of not dvd 821321de1520: P2 M Ground Theory Heights  Heights Model int Cast not mem of not dvd 821321de1520
-- statement:
--   The P2 M Ground Theory Heights  Heights Model int Cast not mem of not dvd 821321de1520 construction uses the P2 M Ground Theory Heights  Heights Model int Cast not mem of not dvd 821321de1520 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L85-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_intCast_not_mem_of_not_dvd_821321de1520 {A : Type*} [CommRing A] {Q : Ideal A} (hQ : Q ≠ ⊤) {p : ℕ}
    (hp : p.Prime) (hpQ : (p : A) ∈ Q) {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) : (s : A) ∉ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«intCast_not_mem_of_not_dvd» := P2M_GroundTheory_Heights__Heights_Model_intCast_not_mem_of_not_dvd_821321de1520
