-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_corollary_8
-- name    : QMCTriFree.Circuit.corollary_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:12.960993+00:00
-- url     : https://prove2.me/theorems/058935a6-9308-4dcf-8c17-4fe65520c88c
-- title:
--   Corollary 8 — $\prod_{k\sim i:x_{ik}\ge0}\sqrt{1-\beta^2x_{ik}^2}\ge\sqrt{1-\beta^2}$ and $\prod_{j\ne k\sim i:x_{ik}\ge0}\sqrt{1-\beta^2x_{ik}^2}\ge\sqrt{1-\beta^2(1-x_{ij})^2}$
-- statement:
--   Let $M$ be feasible for $\mathrm{Lasserre}_2(H)$ with edge values $x_{ij}$, fix an edge $(i,j)$ and $\beta\in[0,1]$. Then
--   1. $\displaystyle\prod_{k\sim i:\ x_{ik}\ge0}\sqrt{1-\beta^2x_{ik}^2}\ \ge\ \sqrt{1-\beta^2}$;
--   2. $\displaystyle\prod_{j\ne k\sim i:\ x_{ik}\ge0}\sqrt{1-\beta^2x_{ik}^2}\ \ge\ \sqrt{1-\beta^2(1-x_{ij})^2}$,
--
--   where $k\sim i$ ranges over the neighbours of $i$ and $j\ne k\sim i$ over the neighbours other than $j$.
--
--   These are the neighbour-product bounds that turn Lemma 12 into Lemma 18 once $\cos2\theta_{ik}=\sqrt{1-\beta^2x_{ik}^2}$.
--
--   **Formalization Note** Only the $x$-part is stated. Part 2 holds as printed, without a sign condition on $x_{ij}$. $\sqrt{\cdot}$ is `Real.sqrt`, which is $0$ on negative arguments.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 8, Corollary 8 (proof p. 27)

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Lasserre

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 8, Corollary 8 (the `x` part): for a feasible `M`, an edge
`(i, j)` and `β ∈ [0, 1]`,
(1) `∏_{k∼i : x_ik ≥ 0} √(1 − β² x_ik²) ≥ √(1 − β²)`, and
(2) `∏_{j≠k∼i : x_ik ≥ 0} √(1 − β² x_ik²) ≥ √(1 − β² (1 − x_ij)²)`. -/
theorem corollary_8 {n : ℕ} (w : Fin n → Fin n → ℝ) (hw : IsWeightedGraph w)
    (M : Matrix (P2 n) (P2 n) ℝ) (hM : IsFeasible M) (i j : Fin n) (hij : i ≠ j)
    (hwij : w i j ≠ 0) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Real.sqrt (1 - β ^ 2) ≤
        ∏ k ∈ (nbrs w i).filter (fun k => 0 ≤ xval M i k),
          Real.sqrt (1 - β ^ 2 * xval M i k ^ 2) ∧
      Real.sqrt (1 - β ^ 2 * (1 - xval M i j) ^ 2) ≤
        ∏ k ∈ ((nbrs w i).erase j).filter (fun k => 0 ≤ xval M i k),
          Real.sqrt (1 - β ^ 2 * xval M i k ^ 2) := by sorry

end QMCTriFree.Circuit
