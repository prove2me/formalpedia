-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_weight_lh0BlockWt_apply
-- name    : ReciprocityTheory.MultiplicativeHeights.weight_lh0BlockWt_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:01.958941+00:00
-- url     : https://prove2.me/theorems/d6d4a85c-4e4c-574d-a5ab-b1303e0e4939
-- title:
--   Multiplicative Heights: weight lh0 Block Wt apply
-- statement:
--   The Multiplicative Heights construction uses the weight lh0 Block Wt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean#L11-L17

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
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
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.weight_lh0BlockWt_apply {B n : ℕ} (b : Fin B) (s : Fin B × Fin n →₀ ℕ) :
    Finsupp.weight (blockIndexWeight (n := n) b) s = ∑ j : Fin n, s (b, j) := by sorry
