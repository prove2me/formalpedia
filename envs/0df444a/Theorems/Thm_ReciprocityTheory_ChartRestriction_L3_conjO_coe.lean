-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_conjO_coe
-- name    : ReciprocityTheory.ChartRestriction.L3.conjO_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:26.054502+00:00
-- url     : https://prove2.me/theorems/3c50b5c6-c7d9-463d-8902-2915eb0008ba
-- title:
--   L3: conj O coe
-- statement:
--   The L3 construction uses the conj O coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsSqAbsNormOfInert.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsSqAbsNormOfInert.lean#L14-L14

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem ReciprocityTheory.ChartRestriction.L3.conjO_coe (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := by sorry
