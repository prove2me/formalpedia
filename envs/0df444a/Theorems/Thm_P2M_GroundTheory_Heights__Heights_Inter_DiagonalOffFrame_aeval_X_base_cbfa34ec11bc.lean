-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_base_cbfa34ec11bc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_base_cbfa34ec11bc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:38.454803+00:00
-- url     : https://prove2.me/theorems/0a442cd4-76b6-41bc-9d37-8e2359020caf
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame aeval X base cbfa34ec11bc: P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame aeval X base cbfa34ec11bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame aeval X base cbfa34ec11bc construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame aeval X base cbfa34ec11bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L97-L100

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_base_cbfa34ec11bc (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (j : ι) : aeval (T.wwCoord x δ e φ a₀ a₁) (X ⟨T.WBlk.base, j⟩ : MRing (T.wwIdx ι ν κ)) =
      algebraMap Ω Φ (x j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffFrame».«aeval_X_base» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_base_cbfa34ec11bc
