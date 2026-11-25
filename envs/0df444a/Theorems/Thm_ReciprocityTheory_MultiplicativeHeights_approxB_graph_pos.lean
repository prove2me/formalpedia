-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_graph_pos
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_graph_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:37.148061+00:00
-- url     : https://prove2.me/theorems/0ee7d286-c72c-4ff0-bdb0-d598bde8ff5c
-- title:
--   Multiplicative Heights: approx B graph pos
-- statement:
--   The Multiplicative Heights construction uses the approx B graph pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L137-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L137-L154

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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_graph_pos {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)))
    (x : ApproxPosIdx r p → ℂ) :
    0 ≤ (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re ∧
    (x ≠ 0 → 0 < (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re) := by sorry
