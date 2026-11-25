-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibSys_finite
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fibSys_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:14.612975+00:00
-- url     : https://prove2.me/theorems/bbaa1059-9b10-4fb0-9906-6af8b08e3ca8
-- title:
--   Geo: fib Sys finite
-- statement:
--   The Geo construction uses the fib Sys finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFibA.lean#L9-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFibA.lean#L9-L140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.fibSys_finite {W : Type*} [Fintype W] (r : W → ℕ) (H : W → MvPolynomial W ℂ)
    (hH : ∀ i, (H i).totalDegree < r i) :
    {w : W → ℂ | ∀ i, w i ^ r i = eval w (H i)}.Finite := by sorry
