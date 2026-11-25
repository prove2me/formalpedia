-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_primeSubfield_exists_div_aa375bf4250e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_primeSubfield_exists_div_aa375bf4250e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:26.815921+00:00
-- url     : https://prove2.me/theorems/a1859f98-3709-4ad4-8ce6-7cdb560928cf
-- title:
--   P2 M Ground Theory Heights  Heights Inter prime Subfield exists div aa375bf4250e: P2 M Ground Theory Heights  Heights Inter prime Subfield exists div aa375bf4250e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter prime Subfield exists div aa375bf4250e construction uses the P2 M Ground Theory Heights  Heights Inter prime Subfield exists div aa375bf4250e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StSemilocResidueFrac.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StSemilocResidueFrac.lean#L11-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem P2M_GroundTheory_Heights__Heights_Inter_primeSubfield_exists_div_aa375bf4250e {E : Type*} [Field E] (c : (⊥ : Subfield E)) :
    ∃ a b : ℤ, (b : (⊥ : Subfield E)) ≠ 0 ∧ c = a / b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«primeSubfield_exists_div» := P2M_GroundTheory_Heights__Heights_Inter_primeSubfield_exists_div_aa375bf4250e
