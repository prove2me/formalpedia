-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_mul_42b9d2eba7a3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_mul_42b9d2eba7a3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:42.889007+00:00
-- url     : https://prove2.me/theorems/23b0c513-c564-49d9-94b9-a809626d5e0d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms loc mul 42b9d2eba7a3: P2 M Ground Theory Heights  Heights Inter Diagonal Forms loc mul 42b9d2eba7a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms loc mul 42b9d2eba7a3 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms loc mul 42b9d2eba7a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L27-L34

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_mul_42b9d2eba7a3 {R : Subalgebra ℤ Ω} {g y z : Ω} (hy : ∃ n : ℕ, g ^ n * y ∈ R)
    (hz : ∃ n : ℕ, g ^ n * z ∈ R) : ∃ n : ℕ, g ^ n * (y * z) ∈ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«loc_mul» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_mul_42b9d2eba7a3
