-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_sub_07568bbd02a8
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_sub_07568bbd02a8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:16.401981+00:00
-- url     : https://prove2.me/theorems/feeab2b0-9b3f-44f3-ba27-385da40da83a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog sub 07568bbd02a8: P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog sub 07568bbd02a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog sub 07568bbd02a8 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog sub 07568bbd02a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L258-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L258-L262

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_sub_07568bbd02a8 {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«isMultiHomog_sub» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_sub_07568bbd02a8
