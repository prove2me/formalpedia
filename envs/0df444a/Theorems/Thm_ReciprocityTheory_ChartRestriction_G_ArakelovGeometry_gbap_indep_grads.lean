-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_indep_grads
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_indep_grads
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:10:11.682774+00:00
-- url     : https://prove2.me/theorems/1124e3b5-5a1e-41b5-b592-2b30ecbdc20f
-- title:
--   Arakelov Geometry: gbap indep grads
-- statement:
--   The Arakelov Geometry construction uses the gbap indep grads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStA.lean#L24-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStA.lean#L24-L89

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_indep_grads {J : Type} [Fintype J] {D c : ℕ} (e : J ≃ Fin (D + 1 + c))
    (P : Ideal (MvPolynomial J ℤ)) (z₀ : J → ℂ) (T : Submodule ℂ (J → ℂ))
    (hT : ∀ w, w ∈ T ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsConeTangent (Int.castRingHom ℂ) P z₀ w)
    (hTd : finrank ℂ T = D + 1) :
    ∃ f : Fin c → MvPolynomial J ℤ, (∀ i, f i ∈ P) ∧
      LinearIndependent ℂ (fun i => grad (fun j => z₀ (e.symm j))
        (map (Int.castRingHom ℂ) (rename e (f i)))) := by sorry
