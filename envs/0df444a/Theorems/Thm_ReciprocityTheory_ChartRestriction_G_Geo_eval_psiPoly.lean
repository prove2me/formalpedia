-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_psiPoly
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.eval_psiPoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:42.294583+00:00
-- url     : https://prove2.me/theorems/2a0cbad4-c2a5-4150-a718-4b56edc91773
-- title:
--   Geo: eval psi Poly
-- statement:
--   The Geo construction uses the eval psi Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFib.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFib.lean#L35-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
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
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]
variable {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.eval_psiPoly (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1))
    (z : (Σ k, ι k) → ℂ) : eval z (psiPoly Ψ j) = Ψ (segre z) j := by sorry
