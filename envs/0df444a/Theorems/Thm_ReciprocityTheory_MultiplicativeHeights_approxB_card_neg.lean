-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_card_neg
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_card_neg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:21.291616+00:00
-- url     : https://prove2.me/theorems/fe9b80fd-6016-4f1c-9fe0-093b0c6acb29
-- title:
--   Multiplicative Heights: approx B card neg
-- statement:
--   The Multiplicative Heights construction uses the approx B card neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L114-L116

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.approxB_card_neg {r p : ℕ} (hp : p ≤ r) :
    Fintype.card {j : Fin r // ¬ (j : ℕ) < p} = r - p := by sorry
