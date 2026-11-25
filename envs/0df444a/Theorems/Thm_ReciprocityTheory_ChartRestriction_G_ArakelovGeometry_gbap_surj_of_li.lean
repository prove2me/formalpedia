-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_surj_of_li
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_surj_of_li
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:09:07.261906+00:00
-- url     : https://prove2.me/theorems/b790b8ec-45ce-5ffa-8eb4-ec805579f662
-- title:
--   Arakelov Geometry: gbap surj of li
-- statement:
--   The Arakelov Geometry construction uses the gbap surj of li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStA.lean#L131-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStA.lean#L131-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MvPolynomial Module ReciprocityTheory.AnForm.R

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_surj_of_li {n c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (p : Fin n → ℂ)
    (hli : LinearIndependent ℂ (fun i => grad p (F i))) :
    Function.Surjective (fun v : Fin n → ℂ => fun i => ∑ j, eval p (pderiv j (F i)) * v j) := by sorry
