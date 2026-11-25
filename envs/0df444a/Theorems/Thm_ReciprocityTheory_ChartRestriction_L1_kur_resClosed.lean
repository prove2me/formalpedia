-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_resClosed
-- name    : ReciprocityTheory.ChartRestriction.L1.kur_resClosed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:45:13.515184+00:00
-- url     : https://prove2.me/theorems/ce39c432-cdea-5c3b-9ff7-7c0db11b1b74
-- title:
--   L1: kur res Closed
-- statement:
--   The L1 construction uses the kur res Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TchOfIntegral.lean#L25-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TchOfIntegral.lean#L25-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TchOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
open Polynomial

theorem ReciprocityTheory.ChartRestriction.L1.kur_resClosed : ResClosed (MaximalUnramifiedExtension l) l := by sorry
