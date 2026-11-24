-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_aeval_diag_eq_5d1249f546d0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_aeval_diag_eq_5d1249f546d0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:50.702808+00:00
-- url     : https://prove2.me/theorems/509b6cc7-4618-4b41-b3ba-fe284be78ec4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Order aeval diag eq 5d1249f546d0: P2 M Ground Theory Heights  Heights Inter Diagonal Order aeval diag eq 5d1249f546d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Order aeval diag eq 5d1249f546d0 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Order aeval diag eq 5d1249f546d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L93-L106

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_aeval_diag_eq_5d1249f546d0 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) {m : ℕ} {h : MRing (T.wwIdx ι ν κ)} (hh : IsMultiHomog h (T.wwDeg m 0)) :
    aeval (T.wwCoord x δ e φ a₀ a₀) h = aeval (T.wwCoord x δ e φ a₀ a₁) h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOrder».«aeval_diag_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_aeval_diag_eq_5d1249f546d0
