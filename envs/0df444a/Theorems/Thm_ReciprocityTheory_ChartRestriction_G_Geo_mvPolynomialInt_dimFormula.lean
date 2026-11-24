-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mvPolynomialInt_dimFormula
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.mvPolynomialInt_dimFormula
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:46.915727+00:00
-- url     : https://prove2.me/theorems/90e1b934-8dc3-4fdf-b9d3-649dfe272a8b
-- title:
--   Geo: mv Polynomial Int dim Formula
-- statement:
--   The Geo construction uses the mv Polynomial Int dim Formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppA.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppA.lean#L8-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

theorem ReciprocityTheory.ChartRestriction.G.Geo.mvPolynomialInt_dimFormula {σ : Type*} [Finite σ] (P Q : Ideal (MvPolynomial σ ℤ))
    [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ Q) + ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by sorry
