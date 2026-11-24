-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_gt_of_comap_int_eq_bot
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_gt_of_comap_int_eq_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:17.5958+00:00
-- url     : https://prove2.me/theorems/870f2e5c-8b9f-4c05-87d7-6f92045c7f9f
-- title:
--   Geo: exists gt of comap int eq bot
-- statement:
--   The Geo construction uses the exists gt of comap int eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L65-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L65-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Ideal

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_gt_of_comap_int_eq_bot {σ A : Type*} [Finite σ] [CommRing A]
    (g : MvPolynomial σ ℤ →+* A) (hg : Function.Surjective g) (p : Ideal A) (hp : p.IsPrime)
    (hb : p.comap (g.comp MvPolynomial.C) = ⊥) : ∃ q : Ideal A, q.IsPrime ∧ p < q := by sorry
