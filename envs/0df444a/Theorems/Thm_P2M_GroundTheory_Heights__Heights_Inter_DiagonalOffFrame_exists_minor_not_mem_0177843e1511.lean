-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_minor_not_mem_0177843e1511
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_minor_not_mem_0177843e1511
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:59.704406+00:00
-- url     : https://prove2.me/theorems/bdd1917a-4104-4fb2-9503-65ff82e2df76
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame exists minor not mem 0177843e1511: P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame exists minor not mem 0177843e1511
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame exists minor not mem 0177843e1511 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame exists minor not mem 0177843e1511 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L18-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L18-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_minor_not_mem_0177843e1511 (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0)
    (q : Ideal (chartRing ℤ x i)) (hq : q.IsPrime) :
    ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, ∃ ψ ∈ T.dualLat B i, ∃ ψ' ∈ T.dualLat B i,
      ∃ m : chartRing ℤ x i, m ∉ q ∧ (m : Ω) = ψ u * ψ' w - ψ w * ψ' u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffFrame».«exists_minor_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_minor_not_mem_0177843e1511
