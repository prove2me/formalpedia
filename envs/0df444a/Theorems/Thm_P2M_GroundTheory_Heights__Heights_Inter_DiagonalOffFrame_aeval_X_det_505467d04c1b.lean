-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_det_505467d04c1b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_det_505467d04c1b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:33.606797+00:00
-- url     : https://prove2.me/theorems/64236269-4182-4bd7-8ca9-f21733b59d57
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame aeval X det 505467d04c1b: P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame aeval X det 505467d04c1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame aeval X det 505467d04c1b construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame aeval X det 505467d04c1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L103-L106

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
omit [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_det_505467d04c1b (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (l : ν) : aeval (T.wwCoord x δ e φ a₀ a₁) (X ⟨T.WBlk.det, l⟩ : MRing (T.wwIdx ι ν κ)) =
      algebraMap Ω Φ (δ l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffFrame».«aeval_X_det» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_det_505467d04c1b
