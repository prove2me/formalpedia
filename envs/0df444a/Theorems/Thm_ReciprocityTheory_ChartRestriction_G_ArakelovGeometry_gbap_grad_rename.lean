-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_grad_rename
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_grad_rename
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:56.093347+00:00
-- url     : https://prove2.me/theorems/d9d90b48-c967-5d56-9b4f-44a2c46f4d4d
-- title:
--   Arakelov Geometry: gbap grad rename
-- statement:
--   The Arakelov Geometry construction uses the gbap grad rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStA.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStA.lean#L12-L22

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_grad_rename {J : Type} [Fintype J] {n : ℕ} (e : J ≃ Fin n) (z₀ : J → ℂ)
    (f : MvPolynomial J ℤ) (j : Fin n) :
    grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e f)) j =
      eval z₀ (pderiv (e.symm j) (map (Int.castRingHom ℂ) f)) := by sorry
