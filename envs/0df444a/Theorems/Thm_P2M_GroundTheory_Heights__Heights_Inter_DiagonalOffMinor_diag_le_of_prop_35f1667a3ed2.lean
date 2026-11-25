-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_diag_le_of_prop_35f1667a3ed2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_diag_le_of_prop_35f1667a3ed2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:31.486497+00:00
-- url     : https://prove2.me/theorems/3f8d3f52-81fa-4570-b0fd-badc71633ba3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor diag le of prop 35f1667a3ed2: P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor diag le of prop 35f1667a3ed2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor diag le of prop 35f1667a3ed2 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor diag le of prop 35f1667a3ed2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffMinor.lean#L44-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffMinor.lean#L44-L84

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
omit [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_diag_le_of_prop_35f1667a3ed2 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) (W : Ideal (MRing (T.wwIdx ι ν κ))) [W.IsPrime] (hW : T.wwIdeal x δ e φ a₀ a₁ ≤ W) (m : κ)
    (hm : (X ⟨.line0, m⟩ : MRing (T.wwIdx ι ν κ)) ∉ W)
    (hprop : ∀ q : κ, (X ⟨.line0, m⟩ * X ⟨.line1, q⟩ - X ⟨.line1, m⟩ * X ⟨.line0, q⟩ :
      MRing (T.wwIdx ι ν κ)) ∈ W) :
    T.wwIdeal x δ e φ a₀ a₀ ≤ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffMinor».«diag_le_of_prop» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_diag_le_of_prop_35f1667a3ed2
