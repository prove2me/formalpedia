-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_le_ringKrullDim_of_isIntegral
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.le_ringKrullDim_of_isIntegral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:49.926735+00:00
-- url     : https://prove2.me/theorems/b3adc315-be02-4d7f-a3d0-647dad0cda6e
-- title:
--   Geo: le ring Krull Dim of is Integral
-- statement:
--   The Geo construction uses the le ring Krull Dim of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L42-L49

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.le_ringKrullDim_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) (hinj : Function.Injective f) (n : ℕ)
    (h : (n : WithBot ℕ∞) ≤ ringKrullDim R) : (n : WithBot ℕ∞) ≤ ringKrullDim S := by sorry
