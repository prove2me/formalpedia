-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_add_right
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_jForm_add_right
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:21.904807+00:00
-- url     : https://prove2.me/theorems/0651481a-db42-412e-81a1-2aecc474adae
-- title:
--   Multiplicative Heights: approx B j Form add right
-- statement:
--   The Multiplicative Heights construction uses the approx B j Form add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L10-L12

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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_jForm_add_right (p : ℕ) {r : ℕ} (x y z : Fin r → ℂ) :
    jForm p x (y + z) = jForm p x y + jForm p x z := by sorry
