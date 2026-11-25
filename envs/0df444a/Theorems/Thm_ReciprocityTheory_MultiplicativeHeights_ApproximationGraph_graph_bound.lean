-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_graph_bound
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.graph_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:12.643121+00:00
-- url     : https://prove2.me/theorems/36980e32-707f-49fd-9ff2-1db444aa4a98
-- title:
--   Approximation Graph: graph bound
-- statement:
--   The Approximation Graph construction uses the graph bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean#L44-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean#L44-L96

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.graph_bound {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (negPart p (∑ j, w j • X j))‖ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ ∧
      3 * (√(r : ℝ) * μ * ‖euc w‖) ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by sorry
