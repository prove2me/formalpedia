-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_of_eq_4cde1a2b5f0a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_of_eq_4cde1a2b5f0a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:21.665079+00:00
-- url     : https://prove2.me/theorems/665a6840-b315-4ba5-95e8-a8c5bbf27db4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog of eq 4cde1a2b5f0a: P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog of eq 4cde1a2b5f0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog of eq 4cde1a2b5f0a construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog of eq 4cde1a2b5f0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L297-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L297-L299

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_of_eq_4cde1a2b5f0a {f : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (h : a = b) :
    IsMultiHomog f b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«isMultiHomog_of_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_of_eq_4cde1a2b5f0a
