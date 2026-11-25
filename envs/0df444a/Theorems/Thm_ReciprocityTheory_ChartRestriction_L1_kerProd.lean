-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kerProd
-- name    : ReciprocityTheory.ChartRestriction.L1.kerProd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:05:54.792913+00:00
-- url     : https://prove2.me/theorems/89b497b3-1b8a-5bb7-bbcb-92859685a1e9
-- title:
--   L1: ker Prod
-- statement:
--   The L1 construction uses the ker Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerProd.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerProd.lean#L10-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.kerProd (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    (hl : l.Prime) (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (e : ℕ) (he : e = 2 ∨ e = 3 ∧ d ≠ 3) :
    KerProdAt d L l e := by sorry
