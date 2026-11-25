-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_map_comp_subst_dde6ca6167d5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_map_comp_subst_dde6ca6167d5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:51.185861+00:00
-- url     : https://prove2.me/theorems/30e61ee6-4d71-4d05-ad1c-5c40f77e0822
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor map comp subst dde6ca6167d5: P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor map comp subst dde6ca6167d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor map comp subst dde6ca6167d5 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Minor map comp subst dde6ca6167d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffMinor.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffMinor.lean#L29-L40

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_map_comp_subst_dde6ca6167d5 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) :
    (Polynomial.mapRingHom (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁))).comp
        (eval₂Hom (Int.castRingHom _) (lineSubst ι ν κ)) =
      (eval₂Hom (Polynomial.C.comp C) (blockSubst (Φ := Φ))).comp
        (T.multiConeMap (T.wwCoord x δ e φ a₀ a₀)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffMinor».«map_comp_subst» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_map_comp_subst_dde6ca6167d5
