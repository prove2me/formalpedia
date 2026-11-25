-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pointsIntegral_degree_zero_eq_mongeAmpereIntegral
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.pointsIntegral_degree_zero_eq_mongeAmpereIntegral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:16.343797+00:00
-- url     : https://prove2.me/theorems/49261b68-f09e-5967-9ea6-8f5d45fa0d93
-- title:
--   Geo: points Integral degree zero eq monge Ampere Integral
-- statement:
--   The Geo construction uses the points Integral degree zero eq monge Ampere Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L81-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L81-L98

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
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
open MvPolynomial ReciprocityTheory.AnForm.M

theorem ReciprocityTheory.ChartRestriction.G.Geo.pointsIntegral_degree_zero_eq_mongeAmpereIntegral (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {n : ℕ} (R : AnLogRes P J (n + 1)) {L : Fin n → HermLine ι}
    {C C' : HermLine ι} (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j))
    (hC : IsSmoothHerm C) (hC' : IsSmoothHerm C') (hC0 : C.a = 0) (hC'0 : C'.a = 0) :
    ptsIntegral P (Fin.cons (fun z => Real.log (C'.h z)) (pot L)) (fun z => Real.log (C.h z)) =
      mInt R.A (Fin.cons (LocPot.ofFun fun x => Real.log (C'.h (R.lift x x)))
        (fun j => potOf R (L j))) (fun x => Real.log (C.h (R.lift x x))) := by sorry
