-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_psiPoly_homog
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.psiPoly_homog
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:54.254981+00:00
-- url     : https://prove2.me/theorems/007e1cb9-fc49-40dd-89e9-728695888206
-- title:
--   Geo: psi Poly homog
-- statement:
--   The Geo construction uses the psi Poly homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFib.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFib.lean#L46-L53

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.psiPoly_homog (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    IsWeightedHomogeneous (blkW ι) (psiPoly Ψ j) (fun _ => 1) := by sorry
