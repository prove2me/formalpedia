-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_ltSeries_lift
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_ltSeries_lift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:04.847997+00:00
-- url     : https://prove2.me/theorems/c77452d1-839d-590f-adb3-8b844b21a564
-- title:
--   Geo: exists lt Series lift
-- statement:
--   The Geo construction uses the exists lt Series lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L7-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L7-L40

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_ltSeries_lift {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum R)), p.length = n →
      ∃ q : LTSeries (PrimeSpectrum S), q.length = n ∧
        q.last.asIdeal.comap (algebraMap R S) = p.last.asIdeal := by sorry
