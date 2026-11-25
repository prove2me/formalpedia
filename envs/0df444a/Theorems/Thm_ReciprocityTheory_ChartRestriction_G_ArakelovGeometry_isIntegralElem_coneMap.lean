-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isIntegralElem_coneMap
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isIntegralElem_coneMap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:12.86525+00:00
-- url     : https://prove2.me/theorems/57cf6b9d-aeb8-4e80-b16e-730a8eaae161
-- title:
--   Arakelov Geometry: is Integral Elem cone Map
-- statement:
--   The Arakelov Geometry construction uses the is Integral Elem cone Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStB.lean#L71-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStB.lean#L71-L110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isIntegralElem_coneMap (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e)
    (q : MvPolynomial J ℤ) :
    (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (coneMap ℤ v q) := by sorry
