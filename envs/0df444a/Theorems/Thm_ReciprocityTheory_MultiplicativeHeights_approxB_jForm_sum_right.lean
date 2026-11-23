-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_sum_right
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_jForm_sum_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:57.977983+00:00
-- url     : https://prove2.me/theorems/2f193a34-2430-4514-948e-96e19467a6e8
-- title:
--   Multiplicative Heights: approx B j Form sum right
-- statement:
--   The Multiplicative Heights construction uses the approx B j Form sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L23-L26

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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_jForm_sum_right (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (x : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p x (∑ j ∈ s, f j) = ∑ j ∈ s, jForm p x (f j) := by sorry
