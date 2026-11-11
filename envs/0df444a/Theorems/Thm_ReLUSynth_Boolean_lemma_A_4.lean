-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_lemma_A_4
-- name    : ReLUSynth.Boolean.lemma_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:11:32.006219+00:00
-- url     : https://prove2.me/theorems/8355d731-6e2f-44e7-856c-c2656d0bac81
-- title:
--   Lemma A.4 — ReLU networks with nonnegative edge weights are monotone and supermodular on the cube, so cannot represent the query target
-- statement:
--   Let $N$ be a ReLU network (any DAG, real parameters) whose edge weights, including those into the affine output, are all nonnegative, with arbitrary hidden biases and an arbitrary output bias. Then $N$ is monotone on the Boolean cube, and supermodular there: for any two coordinates $s\ne t$ and any setting of the others,
--   $$N(1,1)-N(1,0)-N(0,1)+N(0,0)\ \ge\ 0 .$$
--   Consequently such a network cannot represent the query target $g(y)=[\sum_{i,\gamma}2^iy_{i,\gamma}\ge 2^r-1]$, which has a negative mixed difference.
--
--   Differences from the source:
--   - encoding: a permitted network is an arbitrary finite DAG with one output vertex → the computational vertices are numbered 0,…,h in a topological order, the output is vertex h, and an edge between computational vertices goes from a lower to a higher number (Pos.hidEdge); reason: every finite DAG has a topological order (p. 9), and the output, which every computational vertex reaches, is last in it; the same networks up to relabeling
--   - encoding: a ReLU network with real edge weights and biases → any Net ι α with any values W : α → ℝ (no permittedness condition; occurrences may repeat); reason: every real-weighted DAG ReLU network with affine output is such a Net and conversely
--   - generalization: the query target (the restriction of the calibrated f to a clean block, r the calibrated prime) → the query target g on 3r coordinates for every r ≥ 1; reason: the calibrated r is ≥ 7, so the statement specializes to the paper's; the OR-face argument works for every r ≥ 1
--   - generalization: monotone for networks with nonnegative edge weights and arbitrary hidden biases; an arbitrary output bias does not affect the supermodular conclusion → both conclusions (monotone and supermodular) and the non-representation claim for an arbitrary output bias; reason: the output bias adds a constant, which changes neither monotonicity nor any mixed difference, so the statement specializes to the paper's
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 80, Lemma A.4

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Calibrated

namespace ReLUSynth.Boolean

/-- Lemma A.4 (p. 80): a ReLU network (any DAG, any real parameters) whose edge weights, including
the output's, are all nonnegative, with arbitrary hidden and output biases, is monotone and
supermodular on the Boolean cube (every pairwise mixed difference is `≥ 0`). Such a network
cannot represent the query target `g` of Lemma 4.7 (stated for every `r ≥ 1`). -/
theorem lemma_A_4 :
    (∀ {ι α : Type} [Fintype ι] [DecidableEq ι] (N : Net ι α) (W : α → ℝ),
      (∀ (p : Pos ι N.h) (o : α), p.IsEdge → N.occ p = some o → 0 ≤ W o) →
      (∀ x y : ι → Bool, x ≤ y → N.eval W (boolVec x) ≤ N.eval W (boolVec y)) ∧
      (∀ (s t : ι) (x : ι → Bool), s ≠ t →
        0 ≤ mixedDiff (fun y => N.eval W (boolVec y)) s t x)) ∧
    (∀ r : ℕ, 1 ≤ r → ∀ {α : Type} (N : Net (Fin r × Fin 3) α) (W : α → ℝ),
      (∀ (p : Pos (Fin r × Fin 3) N.h) (o : α), p.IsEdge → N.occ p = some o → 0 ≤ W o) →
      ¬ ∀ y : Fin r × Fin 3 → Bool, N.eval W (boolVec y) = bitR (queryTarget r y)) := by sorry

end ReLUSynth.Boolean
