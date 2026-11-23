-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_N2_ncard_places_eq_finrank_iff
-- name    : ReciprocityTheory.ChartRestriction.N2.ncard_places_eq_finrank_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:47.309331+00:00
-- url     : https://prove2.me/theorems/e609768b-33c4-45ec-817f-b27496510f9a
-- title:
--   N2: ncard places eq finrank iff
-- statement:
--   The N2 construction uses the ncard places eq finrank iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/PlaceCounting/RaySplA.lean#L9-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/PlaceCounting/RaySplA.lean#L9-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_PlaceCounting_RaySplA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.N2
open NumberField IsDedekindDomain

theorem ReciprocityTheory.ChartRestriction.N2.ncard_places_eq_finrank_iff (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E ↔
      ∀ W : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ W.asIdeal →
        W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1 := by sorry
