-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_contr_19191a06dc04
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_contr_19191a06dc04
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:33.581035+00:00
-- url     : https://prove2.me/theorems/a7051d6e-c274-5873-8a53-f6c0a49076e1
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame exists contr 19191a06dc04: P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame exists contr 19191a06dc04
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame exists contr 19191a06dc04 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame exists contr 19191a06dc04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L146-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L146-L199

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_contr_19191a06dc04 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) (W : Ideal (MRing (T.wwIdx ι ν κ))) (hW : W.IsPrime)
    (hle : T.wwIdeal x δ e φ a₀ a₁ ≤ W) (hXi : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W) :
    ∃ q : Ideal (chartRing ℤ x i), q.IsPrime ∧ ∀ r : chartRing ℤ x i, r ∉ q →
      ∀ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) →
        aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) → F ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffFrame».«exists_contr» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_contr_19191a06dc04
