-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lt_map
-- name    : ReciprocityTheory.ChartRestriction.L1.lt_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:45:31.402946+00:00
-- url     : https://prove2.me/theorems/82af6915-1d67-4d7d-8e60-3263d594410b
-- title:
--   L1: lt map
-- statement:
--   The L1 construction uses the lt map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L195-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L195-L200

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

theorem ReciprocityTheory.ChartRestriction.L1.lt_map (l : ℕ) (hl : 2 ≤ l) (ε : K) :
    PowerSeries.map φ ((uSer g2 g3).subst (C ε * ltLog K l))
      = (uSer (φ g2) (φ g3)).subst (C (φ ε) * ltLog L l) := by sorry
