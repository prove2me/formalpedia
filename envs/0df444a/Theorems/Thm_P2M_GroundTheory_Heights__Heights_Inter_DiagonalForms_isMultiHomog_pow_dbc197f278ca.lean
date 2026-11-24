-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_pow_dbc197f278ca
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_pow_dbc197f278ca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:27.26561+00:00
-- url     : https://prove2.me/theorems/b9ca2d2d-2dc0-4141-bb36-766e5a0da893
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog pow dbc197f278ca: P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog pow dbc197f278ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog pow dbc197f278ca construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog pow dbc197f278ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L288-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L288-L294

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_pow_dbc197f278ca {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«isMultiHomog_pow» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_pow_dbc197f278ca
