-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_wwDeg_add_3ef7064afb1d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_wwDeg_add_3ef7064afb1d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:22.730554+00:00
-- url     : https://prove2.me/theorems/b059c3eb-80de-415f-b6e4-76b84fa06e72
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame ww Deg add 3ef7064afb1d: P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame ww Deg add 3ef7064afb1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame ww Deg add 3ef7064afb1d construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame ww Deg add 3ef7064afb1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L114-L115

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_wwDeg_add_3ef7064afb1d (N M : ℕ) : T.wwDeg N 0 + T.wwDeg M 0 = T.wwDeg (N + M) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffFrame».«wwDeg_add» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_wwDeg_add_3ef7064afb1d
