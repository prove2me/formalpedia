-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_comap_C_ker_multiConeMap_1f1f0638bfa1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_comap_C_ker_multiConeMap_1f1f0638bfa1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:11.832481+00:00
-- url     : https://prove2.me/theorems/d9846264-970c-4f39-8110-e4693ab15884
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux comap C ker multi Cone Map 1f1f0638bfa1: P2 M Ground Theory Heights  Heights Inter Diag RAux comap C ker multi Cone Map 1f1f0638bfa1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux comap C ker multi Cone Map 1f1f0638bfa1 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux comap C ker multi Cone Map 1f1f0638bfa1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L293-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L293-L297

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_comap_C_ker_multiConeMap_1f1f0638bfa1 {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c c' : (Σ k, ι k) → Φ) :
    (RingHom.ker (T.multiConeMap c)).comap (C : ℤ →+* MRing ι) =
      (RingHom.ker (T.multiConeMap c')).comap (C : ℤ →+* MRing ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«comap_C_ker_multiConeMap» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_comap_C_ker_multiConeMap_1f1f0638bfa1
