-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mult_map
-- name    : ReciprocityTheory.ChartRestriction.L1.mult_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:45:22.972531+00:00
-- url     : https://prove2.me/theorems/c9c819f4-7faa-4a0f-8446-1c4d7b806796
-- title:
--   L1: mult map
-- statement:
--   The L1 construction uses the mult map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L190-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L190-L193

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

theorem ReciprocityTheory.ChartRestriction.L1.mult_map (b : K) :
    PowerSeries.map φ ((uSer g2 g3).subst (C b * lgS g2 g3))
      = (uSer (φ g2) (φ g3)).subst (C (φ b) * lgS (φ g2) (φ g3)) := by sorry
