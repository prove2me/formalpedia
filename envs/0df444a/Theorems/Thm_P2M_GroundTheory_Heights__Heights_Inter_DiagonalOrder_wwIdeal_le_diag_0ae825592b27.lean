-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_wwIdeal_le_diag_0ae825592b27
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_wwIdeal_le_diag_0ae825592b27
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:09.932633+00:00
-- url     : https://prove2.me/theorems/8bc29fd6-509f-408d-99af-e31ed74e1002
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Order ww Ideal le diag 0ae825592b27: P2 M Ground Theory Heights  Heights Inter Diagonal Order ww Ideal le diag 0ae825592b27
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Order ww Ideal le diag 0ae825592b27 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Order ww Ideal le diag 0ae825592b27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L83-L91

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_wwIdeal_le_diag_0ae825592b27 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (ha : AlgebraicIndependent Ω a) :
    T.wwIdeal x δ e φ (a 0) (a 1) ≤ T.wwIdeal x δ e φ (a 0) (a 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOrder».«wwIdeal_le_diag» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_wwIdeal_le_diag_0ae825592b27
