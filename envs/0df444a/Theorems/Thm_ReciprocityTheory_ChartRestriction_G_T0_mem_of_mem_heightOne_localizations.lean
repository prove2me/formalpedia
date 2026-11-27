-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_of_mem_heightOne_localizations
-- name    : ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:39.233192+00:00
-- url     : https://prove2.me/theorems/c1779534-e1db-47ee-afe3-57146deac1f2
-- title:
--   T0: mem of mem height One localizations
-- statement:
--   The T0 construction uses the mem of mem height One localizations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegKrull.lean#L64-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegKrull.lean#L64-L188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegKrull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open KrullColonIdeal

theorem ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ a s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K a) :
    ∃ r : R, algebraMap R K r = x := by sorry
