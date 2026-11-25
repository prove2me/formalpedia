-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_wpNum_map
-- name    : ReciprocityTheory.ChartRestriction.L1.wpNum_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:11.37333+00:00
-- url     : https://prove2.me/theorems/ac43518f-5e9f-5fae-974c-90518b5b21b9
-- title:
--   L1: wp Num map
-- statement:
--   The L1 construction uses the wp Num map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L147-L151

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

theorem ReciprocityTheory.ChartRestriction.L1.wpNum_map : PowerSeries.map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by sorry
