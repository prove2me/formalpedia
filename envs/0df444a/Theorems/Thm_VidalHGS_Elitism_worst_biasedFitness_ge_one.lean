-- Prove2me | Theorems.Thm_VidalHGS_Elitism_worst_biasedFitness_ge_one
-- name    : VidalHGS.Elitism.worst_biasedFitness_ge_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:25:06.433417+00:00
-- url     : https://prove2.me/theorems/802d002a-cbb8-45c8-bc6a-631b74e83a7d
-- title:
--   p. 17, Section 4.6, proof of the Proposition — the worst individual has fit = 1 and BF ≥ 1
-- statement:
--   Let $P$ be a subpopulation with $|P| \ge 2$, let $\mathit{nbElit}$ satisfy $\mathit{nbElit} + 1 \le |P|$, and suppose the set $X(P)$ of non-best individuals having a clone is empty. Let $W \in P$ be an individual with the worst fitness, i.e. $c(K) \le c(W)$ for all $K \in P$. Then
--   $$\mathit{fit}_P(W) = 1 \qquad\text{and}\qquad BF_P(W) = \mathit{fit}_P(W) + \Bigl(1 - \frac{\mathit{nbElit}}{|P| - 1}\Bigr) \times \mathit{dc}_P(W) \ge 1.$$
--
--   This is the first sentence of the proof of the elitism Proposition: the worst individual lies in the "removal zone" $BF \ge 1$.
--
--   **Formalization Note.** The paper speaks of "the individual with the worst fitness". The hypothesis $X(P) = \emptyset$ is the branch of the survivor-selection procedure in which this step is used; it forces the costs in $P$ to be pairwise distinct (two individuals of equal cost are clones, and at most one of them is the best solution), so the worst individual is unique and its rank is exactly $1$. The size conditions $|P| \ge 2$ and $\mathit{nbElit} \le |P| - 1$ are left implicit in the paper; they make the denominator positive and the coefficient of $\mathit{dc}$ nonnegative. The proof calls this individual $I$; it is $W$ here.
-- source:
--   Vidal, Crainic, Gendreau, Lahrichi and Rei, A Hybrid Genetic Algorithm for Multi-Depot and Periodic Vehicle Routing Problems, CIRRELT-2010-34 (July 2010), p. 17, Section 4.6, proof of the Proposition (first sentence)

import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

namespace VidalHGS.Elitism

/-- Section 4.6, p. 17, proof of the Proposition: when `X = ∅` (so that costs in `P` are
pairwise distinct), the individual `W` with the worst fitness has `fit(W) = 1` and
`BF(W) ≥ 1`, provided `nbElit ≤ nbIndiv − 1` and `nbIndiv ≥ 2`. -/
theorem worst_biasedFitness_ge_one {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (P : Finset α) (W : α)
    (hX : cloneSet c δ best P = ∅) (hcard : 2 ≤ P.card) (hsize : nbElit + 1 ≤ P.card)
    (hW : W ∈ P) (hworst : ∀ K ∈ P, c K ≤ c W) :
    fitRank c P W = 1 ∧ 1 ≤ biasedFitness c Δ nbElit P W := by sorry

end VidalHGS.Elitism
