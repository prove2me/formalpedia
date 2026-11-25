-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kerProd_ideal
-- name    : ReciprocityTheory.ChartRestriction.L1.kerProd_ideal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:46:35.104039+00:00
-- url     : https://prove2.me/theorems/1e6b8fe1-1b71-5820-b1ef-87daf46e9c25
-- title:
--   L1: ker Prod ideal
-- statement:
--   The L1 construction uses the ker Prod ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerIdeal.lean#L33-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerIdeal.lean#L33-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedGcd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerIdeal
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

theorem ReciprocityTheory.ChartRestriction.L1.kerProd_ideal (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L)
    (l : ℕ) (hl : l.Prime) (h3 : 3 ∣ d) (hd3 : d ≠ 3) : KerProdAt d L l 3 := by sorry
