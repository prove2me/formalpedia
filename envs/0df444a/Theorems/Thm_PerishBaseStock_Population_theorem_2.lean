-- Prove2me | Theorems.Thm_PerishBaseStock_Population_theorem_2
-- name    : PerishBaseStock.Population.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:54.852887+00:00
-- url     : https://prove2.me/theorems/8feb97e8-7540-47c9-92ff-84a23128f917
-- title:
--   Theorem 2 — under FIFO the gap of $\pi_{\widetilde S}$ is at most $K_1e^{-K_2n}$ in the population size $n$
-- statement:
--   Consider the FIFO perishable inventory system with lifetime $m\ge1$, unit costs $h>0$, $p>0$, $\theta\ge0$, zero lead time and lost sales, and suppose the generic one-period demand takes the population form (7): $D(n)=\sum_{j=1}^{N(n)}\hat D_j$, where the $\hat D_j$ are i.i.d. non-negative with finite variance and mean $\mathbb E[\hat D_1]>0$, and $N(n)=\sup\{N:\sum_{k=1}^NX_k/n\le1\}$ for i.i.d. non-negative $X_k$ with mean one, finite variance and $\mathbb E[e^{sX_1}]<\infty$ for some $s>0$, independent of the $\hat D_j$. Let $C_n$, $\mathrm{OPT}_n$ and $\widetilde S_n$ denote the base-stock cost, the optimal long-run average cost over all admissible policies, and a minimizer of the heuristic cost $\widetilde C_n$ of (4), in the system with demand $D(n)$.
--
--   There exist two positive constants $K_1$ and $K_2$ and an integer $n_0$ such that, for every $n\ge n_0$ and every minimizer $\widetilde S_n$,
--   $$
--   C_n(\widetilde S_n)-\mathrm{OPT}_n\le K_1\,e^{-K_2 n}.
--   $$
--
--   The heuristic base-stock policy is therefore asymptotically optimal as the demand population grows, with an exponentially small optimality gap.
--
--   **Formalization Note** The gap is stated as $C_n(\widetilde S_n)\le\mathrm{OPT}_n+K_1e^{-K_2n}$ in $[0,\infty]$, equivalent because $\mathrm{OPT}_n<\infty$. $K_1$ and $K_2$ may depend on $m,h,p,\theta$ and the laws of $\hat D_1$ and $X_1$, but not on $n$. The hypothesis $\mathbb E[\hat D_1]>0$ is the paper's standing assumption $\mathbb E[D]>0$ (it also follows from the family being a family of demand laws with positive mean).
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 12, Theorem 2

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-- **Theorem 2** (Bu, Gong & Chao, p. 12). Suppose the generic demand takes form (7). There exist
positive constants `K₁`, `K₂` such that `C_n(S̃_n) - OPT_n ≤ K₁ e^{-K₂ n}` for all sufficiently
large `n`, for every minimizer `S̃_n` of `C̃_n`. The gap is stated as `C_n(S̃_n) ≤ OPT_n + K₁e^{-K₂n}`
in `ℝ≥0∞`. The parameters `m, h, p, θ` are fixed and general. -/
theorem theorem_2 (c : PerishBaseStock.Lifetime.Params) (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ K₂ : ℝ, 0 < K₂ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ S : ℝ≥0, PerishBaseStock.Lifetime.IsHeuristicLevel (P n) c S →
        baseStockCost (P n) c S ≤
          OPT (P n) c + ENNReal.ofReal (K₁ * Real.exp (-(K₂ * (n : ℝ)))) := by sorry

end PerishBaseStock.Population
