-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_unif_mem
-- name    : ReciprocityTheory.ChartRestriction.G.T0.unif_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:57.824731+00:00
-- url     : https://prove2.me/theorems/2b74c2be-ad3a-4b75-9a72-1312f1b03518
-- title:
--   T0: unif mem
-- statement:
--   The T0 construction uses the unif mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L71-L81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
omit [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.unif_mem [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (Data.unif la : 𝓞 K) ∈ la.asIdeal ∧ (Data.unif la : 𝓞 K) ∉ la.asIdeal ^ 2 := by sorry
