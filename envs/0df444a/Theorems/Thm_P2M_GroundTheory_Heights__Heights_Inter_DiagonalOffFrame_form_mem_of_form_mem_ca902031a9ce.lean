-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_form_mem_of_form_mem_ca902031a9ce
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_form_mem_of_form_mem_ca902031a9ce
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:46.145165+00:00
-- url     : https://prove2.me/theorems/b104e572-c421-54e3-934b-6015465d8180
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame form mem of form mem ca902031a9ce: P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame form mem of form mem ca902031a9ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame form mem of form mem ca902031a9ce construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame form mem of form mem ca902031a9ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L124-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L124-L144

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_form_mem_of_form_mem_ca902031a9ce (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) {W : Ideal (MRing (T.wwIdx ι ν κ))} (hW : W.IsPrime) (hle : T.wwIdeal x δ e φ a₀ a₁ ≤ W)
    {i : ι} (hXi : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W) {r : Ω} {N M : ℕ}
    {F G : MRing (T.wwIdx ι ν κ)} (hF : IsMultiHomog F (T.wwDeg N 0))
    (hFv : aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r))
    (hG : IsMultiHomog G (T.wwDeg M 0))
    (hGv : aeval (T.wwCoord x δ e φ a₀ a₁) G = algebraMap Ω Φ (x i ^ M * r)) (hFW : F ∈ W) : G ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffFrame».«form_mem_of_form_mem» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_form_mem_of_form_mem_ca902031a9ce
