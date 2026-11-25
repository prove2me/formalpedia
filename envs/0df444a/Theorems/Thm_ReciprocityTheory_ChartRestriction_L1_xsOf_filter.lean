-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_xsOf_filter
-- name    : ReciprocityTheory.ChartRestriction.L1.xsOf_filter
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:19.478293+00:00
-- url     : https://prove2.me/theorems/9e9af5ee-3863-5ff8-b948-50c656959b7a
-- title:
--   L1: xs Of filter
-- statement:
--   The L1 construction uses the xs Of filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerIdeal.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerIdeal.lean#L13-L26

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

theorem ReciprocityTheory.ChartRestriction.L1.xsOf_filter (L : PeriodPair) (α β : ℂ) (hα : MulStable L α) (hβ : MulStable L β) (T T' : Finset ℂ)
    (hT : IsHalfReps L α T) (hT' : IsHalfReps L β T') :
    xsOf L (T.filter (fun P => β * P ∈ L.lattice)) = xsOf L T ∩ xsOf L T' := by sorry
