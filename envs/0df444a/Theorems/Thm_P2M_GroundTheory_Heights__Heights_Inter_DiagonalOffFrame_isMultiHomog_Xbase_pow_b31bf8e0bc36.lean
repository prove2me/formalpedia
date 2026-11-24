-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_isMultiHomog_Xbase_pow_b31bf8e0bc36
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_isMultiHomog_Xbase_pow_b31bf8e0bc36
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:14.691817+00:00
-- url     : https://prove2.me/theorems/1644b25c-46dc-432b-bccd-9b3186290833
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame is Multi Homog Xbase pow b31bf8e0bc36: P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame is Multi Homog Xbase pow b31bf8e0bc36
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame is Multi Homog Xbase pow b31bf8e0bc36 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame is Multi Homog Xbase pow b31bf8e0bc36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L108-L112

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
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_isMultiHomog_Xbase_pow_b31bf8e0bc36 (j : ι) (M : ℕ) :
    IsMultiHomog ((X ⟨T.WBlk.base, j⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffFrame».«isMultiHomog_Xbase_pow» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_isMultiHomog_Xbase_pow_b31bf8e0bc36
