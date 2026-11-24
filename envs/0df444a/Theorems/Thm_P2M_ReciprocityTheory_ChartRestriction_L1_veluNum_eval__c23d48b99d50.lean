-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_veluNum_eval__c23d48b99d50
-- name    : P2M_ReciprocityTheory_ChartRestriction_L1_veluNum_eval__c23d48b99d50
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:43.847925+00:00
-- url     : https://prove2.me/theorems/c8f21e37-b307-432c-8e32-3554021f65da
-- title:
--   P2 M Reciprocity Theory Chart Restriction L1 velu Num eval  c23d48b99d50: P2 M Reciprocity Theory Chart Restriction L1 velu Num eval  c23d48b99d50
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction L1 velu Num eval  c23d48b99d50 construction uses the P2 M Reciprocity Theory Chart Restriction L1 velu Num eval  c23d48b99d50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L41-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
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
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {K : Type} [Field K] [CharZero K] [DecidableEq K] (g2 g3 : K) (xs : Finset K)

theorem P2M_ReciprocityTheory_ChartRestriction_L1_veluNum_eval__c23d48b99d50 (t : K) :
    (veluNum g2 g3 xs).eval t = t * (rootPoly xs).eval t ^ 2
      + ∑ x ∈ xs, (fW g2 g3 x + fW' g2 x / 2 * (t - x)) * (rootPoly (xs.erase x)).eval t ^ 2 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«L1».«veluNum_eval'» := P2M_ReciprocityTheory_ChartRestriction_L1_veluNum_eval__c23d48b99d50
