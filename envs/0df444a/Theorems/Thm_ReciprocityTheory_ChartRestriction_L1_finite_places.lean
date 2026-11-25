-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_finite_places
-- name    : ReciprocityTheory.ChartRestriction.L1.finite_places
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:55.715373+00:00
-- url     : https://prove2.me/theorems/781638ec-cca7-45b0-bfa7-05a534ec2c7c
-- title:
--   L1: finite places
-- statement:
--   The L1 construction uses the finite places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModSepInt.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModSepInt.lean#L57-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.finite_places (E : Type*) [Field E] [NumberField E] {n : ℤ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 E) | (n : 𝓞 E) ∈ v.asIdeal}.Finite := by sorry
