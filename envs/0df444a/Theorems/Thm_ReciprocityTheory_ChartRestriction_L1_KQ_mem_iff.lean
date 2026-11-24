-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KQ_mem_iff
-- name    : ReciprocityTheory.ChartRestriction.L1.KQ_mem_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:46.181202+00:00
-- url     : https://prove2.me/theorems/07d62e20-c45e-43ea-b1af-28a715b93877
-- title:
--   L1: KQ mem iff
-- statement:
--   The L1 construction uses the KQ mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModQuadInt.lean#L14-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModQuadInt.lean#L14-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt
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

theorem ReciprocityTheory.ChartRestriction.L1.KQ_mem_iff (d : ℕ) (z : ℂ) : z ∈ KQ d ↔ ∃ u v : ℚ, z = u + v * sqD d := by sorry
