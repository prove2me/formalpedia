-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_mem_divSupp_of_divCycle_ne_zero_8a9d5c46595e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_mem_divSupp_of_divCycle_ne_zero_8a9d5c46595e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:09.257733+00:00
-- url     : https://prove2.me/theorems/83f9eaed-9799-442c-80f9-942dd0728fcc
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux mem div Supp of div Cycle ne zero 8a9d5c46595e: P2 M Ground Theory Heights  Heights Inter Diag RAux mem div Supp of div Cycle ne zero 8a9d5c46595e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux mem div Supp of div Cycle ne zero 8a9d5c46595e construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux mem div Supp of div Cycle ne zero 8a9d5c46595e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L179-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L179-L183

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_mem_divSupp_of_divCycle_ne_zero_8a9d5c46595e {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (h : divCycle P s W ≠ 0) : W ∈ divSupp P s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«mem_divSupp_of_divCycle_ne_zero» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_mem_divSupp_of_divCycle_ne_zero_8a9d5c46595e
