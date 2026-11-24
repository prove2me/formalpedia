-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_add_71b7a804ca0a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_add_71b7a804ca0a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:30.022059+00:00
-- url     : https://prove2.me/theorems/c8e8736b-1bf1-43f1-a8ad-7e8f9e86372d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms loc add 71b7a804ca0a: P2 M Ground Theory Heights  Heights Inter Diagonal Forms loc add 71b7a804ca0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms loc add 71b7a804ca0a construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms loc add 71b7a804ca0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L18-L25

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
variable {Ω : Type*} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_add_71b7a804ca0a {R : Subalgebra ℤ Ω} {g y z : Ω} (hg : g ∈ R) (hy : ∃ n : ℕ, g ^ n * y ∈ R)
    (hz : ∃ n : ℕ, g ^ n * z ∈ R) : ∃ n : ℕ, g ^ n * (y + z) ∈ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«loc_add» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_add_71b7a804ca0a
