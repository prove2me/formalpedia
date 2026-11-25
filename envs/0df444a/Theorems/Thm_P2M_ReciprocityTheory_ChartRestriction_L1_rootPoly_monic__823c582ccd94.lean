-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_rootPoly_monic__823c582ccd94
-- name    : P2M_ReciprocityTheory_ChartRestriction_L1_rootPoly_monic__823c582ccd94
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:18:36.497595+00:00
-- url     : https://prove2.me/theorems/891c5f20-ab9a-42d5-b185-8bef48efbb86
-- title:
--   P2 M Reciprocity Theory Chart Restriction L1 root Poly monic  823c582ccd94: P2 M Reciprocity Theory Chart Restriction L1 root Poly monic  823c582ccd94
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction L1 root Poly monic  823c582ccd94 construction uses the P2 M Reciprocity Theory Chart Restriction L1 root Poly monic  823c582ccd94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedGcd.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedGcd.lean#L10-L11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedGcd
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

theorem P2M_ReciprocityTheory_ChartRestriction_L1_rootPoly_monic__823c582ccd94 {E : Type} [Field E] (xs : Finset E) : (rootPoly xs).Monic := by sorry

alias «ReciprocityTheory».«ChartRestriction».«L1».«rootPoly_monic'» := P2M_ReciprocityTheory_ChartRestriction_L1_rootPoly_monic__823c582ccd94
