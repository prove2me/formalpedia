-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_eq_finsum_b745b6d310f8
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_eq_finsum_b745b6d310f8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:52.439153+00:00
-- url     : https://prove2.me/theorems/370fb1e3-4983-4549-ad5f-8fead7444fa7
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux cyc R eq finsum b745b6d310f8: P2 M Ground Theory Heights  Heights Inter Diag RAux cyc R eq finsum b745b6d310f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux cyc R eq finsum b745b6d310f8 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux cyc R eq finsum b745b6d310f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L147-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L147-L156

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_eq_finsum_b745b6d310f8 (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = ∑ᶠ W, (divCycle P s W : ℝ) * cycTerm I L W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«cycR_eq_finsum» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_eq_finsum_b745b6d310f8
