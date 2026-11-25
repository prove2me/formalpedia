-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_frame_rel_a432b4a776a4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_frame_rel_a432b4a776a4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:45.937903+00:00
-- url     : https://prove2.me/theorems/d88dd767-5d73-4527-9478-0d6cab081781
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor frame rel a432b4a776a4: P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor frame rel a432b4a776a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor frame rel a432b4a776a4 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor frame rel a432b4a776a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffMinor.lean#L86-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffMinor.lean#L86-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffMinor
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
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_frame_rel_a432b4a776a4 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (B : ChartBundle ℤ x 2 E) (hsec : T.IsTwistedDualSec B φ) (hdet : T.IsTwistedDetGen B e δ) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) (l : ν) (k k' : κ) (N : ℕ) (F : MRing (T.wwIdx ι ν κ))
    (hF : IsMultiHomog F (T.wwDeg (N + 3) 0))
    (hFv : aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * δ l * dualMinor e φ k k')) (p : κ) :
    ∃ (n : ℕ) (α β : MRing (T.wwIdx ι ν κ)),
      X ⟨.base, i⟩ ^ n * F * X ⟨.line0, p⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩ ∈
          T.wwIdeal x δ e φ a₀ a₁ ∧
        X ⟨.base, i⟩ ^ n * F * X ⟨.line1, p⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩ ∈
          T.wwIdeal x δ e φ a₀ a₁ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffMinor».«frame_rel» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_frame_rel_a432b4a776a4
