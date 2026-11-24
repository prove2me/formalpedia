-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multiConeMap_eq_f5c45a24f8f1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multiConeMap_eq_f5c45a24f8f1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:35.47037+00:00
-- url     : https://prove2.me/theorems/e811f448-d4d1-471e-871e-5f360c161ea2
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Order multi Cone Map eq f5c45a24f8f1: P2 M Ground Theory Heights  Heights Inter Diagonal Order multi Cone Map eq f5c45a24f8f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Order multi Cone Map eq f5c45a24f8f1 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Order multi Cone Map eq f5c45a24f8f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L72-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
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
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
omit [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multiConeMap_eq_f5c45a24f8f1 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (b : Fin 2 → Φ) :
    T.multiConeMap (T.wwCoord x δ e φ (b 0) (b 1)) =
      (MvPolynomial.map (aeval b : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom).comp (polyConeMap x δ e φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOrder».«multiConeMap_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multiConeMap_eq_f5c45a24f8f1
