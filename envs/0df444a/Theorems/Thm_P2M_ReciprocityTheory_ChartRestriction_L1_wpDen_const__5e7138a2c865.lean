-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_wpDen_const__5e7138a2c865
-- name    : P2M_ReciprocityTheory_ChartRestriction_L1_wpDen_const__5e7138a2c865
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:40.228904+00:00
-- url     : https://prove2.me/theorems/4ee18188-7b0c-4c94-a935-1ceb7e849fc4
-- title:
--   P2 M Reciprocity Theory Chart Restriction L1 wp Den const  5e7138a2c865: P2 M Reciprocity Theory Chart Restriction L1 wp Den const  5e7138a2c865
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction L1 wp Den const  5e7138a2c865 construction uses the P2 M Reciprocity Theory Chart Restriction L1 wp Den const  5e7138a2c865 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L159-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L159-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
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
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)

theorem P2M_ReciprocityTheory_ChartRestriction_L1_wpDen_const__5e7138a2c865 {K : Type} [Field K] (g2 g3 : K) : constantCoeff (wpDen g2 g3) = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«L1».«wpDen_const'» := P2M_ReciprocityTheory_ChartRestriction_L1_wpDen_const__5e7138a2c865
