-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_algebraicIndependent_sumElim
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.algebraicIndependent_sumElim
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:32.895851+00:00
-- url     : https://prove2.me/theorems/0b5517f8-7ed4-4cd1-88b3-2a1e1dd64b02
-- title:
--   Geo: algebraic Independent sum Elim
-- statement:
--   The Geo construction uses the algebraic Independent sum Elim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodG.lean#L41-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodG.lean#L41-L105

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.algebraicIndependent_sumElim (P : Ideal (MRing ι)) (hP : P.IsPrime) (hH : IsHorizontal P)
    (hhom : IsMultiHomogIdeal P) (k0 : K) (i0 : (k : K) → ι k)
    (hi0 : ∀ k, (X ⟨k, i0 k⟩ : MRing ι) ∉ P) {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ)
    (hind : AlgebraicIndependent ℚ (forms (segQ P) L)) :
    AlgebraicIndependent ℚ (Sum.elim (forms (segQ P) L)
      (fun k' : {k // k ≠ k0} => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩))) := by sorry
