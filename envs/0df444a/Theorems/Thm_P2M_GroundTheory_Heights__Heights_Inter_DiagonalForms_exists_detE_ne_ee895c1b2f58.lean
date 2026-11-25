-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_detE_ne_ee895c1b2f58
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_detE_ne_ee895c1b2f58
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:31.377137+00:00
-- url     : https://prove2.me/theorems/4e991fa3-1814-44b5-8b06-799e942209b8
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists det E ne ee895c1b2f58: P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists det E ne ee895c1b2f58
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists det E ne ee895c1b2f58 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists det E ne ee895c1b2f58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L141-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L141-L148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
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
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_detE_ne_ee895c1b2f58 (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0) (e : Module.Basis (Fin 2) Ω E) :
    ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, T.detE e u w ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«exists_detE_ne» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_detE_ne_ee895c1b2f58
