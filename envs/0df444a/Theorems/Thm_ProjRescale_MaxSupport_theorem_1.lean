-- Prove2me | Theorems.Thm_ProjRescale_MaxSupport_theorem_1
-- name    : ProjRescale.MaxSupport.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:27.92751+00:00
-- url     : https://prove2.me/theorems/054caf78-4c36-4879-9f4e-0c753690516d
-- title:
--   Theorem 1, p. 8 — Algorithm 2 terminates with J = J(L), Ĵ = J(L⊥) and maximum support solutions (corrected: k = max{1, ⌈log₂log₂(1/m)⌉+1}, rescalings ≤ 2n(2^k − 1 + k))
-- statement:
--   Let $n \ge 1$ and let $L \subseteq \mathbb R^n$ be a linear subspace. Write
--
--   $$m = \min\{\sigma(L), \sigma(L^\perp)\}, \qquad k = \max\big\{1,\ \lceil \log_2 \log_2(1/m) \rceil + 1\big\}.$$
--
--   Run Algorithm 2 (Maximum support) on $L$, with any admissible behaviour of the basic procedure inside each call of Algorithm 1. Then:
--
--   1. **(progress)** every non-halted state reachable by the algorithm has an admissible next step;
--   2. **(termination)** there is no infinite execution;
--   3. **(main iterations, (6))** no execution starts a main iteration beyond the $k$-th;
--   4. **(rescaling steps, (7))** the total number of rescaling steps performed is at most
--   $$2n\,(2^k - 1 + k);$$
--   5. **(correctness)** upon termination with outputs $(x, J)$ and $(\hat x, \hat J)$, the algorithm has identified $J = J(L)$ and $\hat J = J(L^\perp)$, and found $x \in L \cap \mathbb R^n_+$ and $\hat x \in L^\perp \cap \mathbb R^n_+$ with $x_j > 0$ for all $j \in J$ and $\hat x_j > 0$ for all $j \in \hat J$.
--
--   Here $J(L)$ is the maximum support index set and $\sigma(L)$ the condition measure of $L$ (with $\sigma(L) = 1$ when $J(L) = \emptyset$), so $m \in (0,1]$. The theorem says that a maximum support solution of the pair of feasibility problems $x \in L \cap \mathbb R^n_+$, $\hat x \in L^\perp \cap \mathbb R^n_+$ is found after $O(\log\log(1/m))$ guessing rounds and $O(n\log(1/m))$ rescaling steps, with no knowledge of $\sigma(L)$ or $\sigma(L^\perp)$.
--
--   **Formalization Note** Algorithm 2 is the transition relation `A2Step L` started at `A2Init n` ($\sigma = 1/2$, main iteration 1), with the two calls of Algorithm 1 run step by step inside it; `iter` is the index of the current main iteration and `rescalings` the number of rescaling steps performed so far (including those of a running call). Clauses 3 and 4 bound these counters at every reachable state, which is the same as bounding them at termination because both counters only increase. $\lceil\cdot\rceil$ in $k$ is `Int.ceil` followed by `Int.toNat`, and $\log_2$ is `Real.logb 2`.
--
--   Differences from the source:
--   - correction: (6) $k = \lceil\log_2\log_2(1/m)\rceil + 1$ → $k = \max\{1, \lceil\log_2\log_2(1/m)\rceil + 1\}$; reason: (6) is $\le 0$ for $m \in (2^{-1/2}, 1)$ and undefined at $m = 1$, while every execution performs main iteration 1; counterexample $n = 2$, $L = \mathrm{span}\{(1, 0.8)\}$: $\sigma(L) = 0.8$, $J(L^\perp) = \emptyset$, $m = 0.8$, (6) gives $\lceil -1.64\rceil + 1 = 0$. For $m \le 2^{-1/2}$ the corrected $k$ equals (6).
--   - correction: (7) $4n\lceil\log_2(1/m)\rceil$ → $2n(2^k - 1 + k)$; reason: a call of Algorithm 1 with guess $\sigma$ can perform $n(\lfloor\log_2(1/\sigma)\rfloor + 1)$ rescaling steps (Proposition 1, corrected), and the proof's sum over main iterations is $\sum_{i=1}^k 2n(2^{i-1} + 1) = 2n(2^k - 1 + k)$; counterexample $n = 1$, $L = \mathbb R$: $m = 1$, (7) gives $0$, but $\mathcal J(L^\perp, 1/2)$ with $L^\perp = \{0\}$ forces 2 rescaling steps.
--   - encoding: $n \ge 1$ implicit → hypothesis $0 < n$; reason: for $n = 0$, $\Delta(\{1,\dots,n\}) = \emptyset$ and Algorithm 1 cannot run, so the case is undefined on the page.
--   - encoding: "upon termination … the algorithm terminates after at most $k$ main iterations … the total number of rescaling steps … is bounded above by" → progress, no infinite execution, the counter bounds at every reachable state, and correctness at every reachable halted state of the transition relation, over every admissible basic-procedure answer; reason: the basic procedure is any procedure satisfying step 3 of Algorithm 1, so the claim is about every execution.
-- source:
--   Peña & Soheili, Projection and rescaling algorithm for finding maximum support solutions to polyhedral conic systems, arXiv:2003.08911v3, p. 8, Theorem 1 (Equations (6) and (7)), Algorithm 2

import Mathlib
import Definitions.Def_ProjRescale_MaxSupport_Setting

namespace ProjRescale.MaxSupport

/-- Theorem 1, p. 8, corrected. Write `m = min{σ(L), σ(L⊥)}` and
`k = max{1, ⌈log₂ log₂(1/m)⌉ + 1}`. For every admissible behaviour of the basic procedure,
Algorithm 2 can always continue until it halts, has no infinite execution, never starts a main
iteration beyond `k`, performs at most `2n(2^k − 1 + k)` rescaling steps in total, and upon
termination returns `J = J(L)`, `Ĵ = J(L⊥)` and `x ∈ L ∩ ℝⁿ₊`, `x̂ ∈ L⊥ ∩ ℝⁿ₊` with `x_J > 0`,
`x̂_Ĵ > 0`. -/
theorem theorem_1 (n : ℕ) (hn : 0 < n) (L : Submodule ℝ (E n)) :
    (∀ s, Relation.ReflTransGen (A2Step L) (A2Init n) s → ¬ s.IsDone →
        ∃ s', A2Step L s s') ∧
      (¬ ∃ f : ℕ → A2State n, f 0 = A2Init n ∧ ∀ t, A2Step L (f t) (f (t + 1))) ∧
      (∀ s, Relation.ReflTransGen (A2Step L) (A2Init n) s →
        s.iter ≤ kIter (min (condMeasure L) (condMeasure Lᗮ))) ∧
      (∀ s, Relation.ReflTransGen (A2Step L) (A2Init n) s →
        s.rescalings ≤ 2 * n * (2 ^ kIter (min (condMeasure L) (condMeasure Lᗮ)) - 1 +
          kIter (min (condMeasure L) (condMeasure Lᗮ)))) ∧
      (∀ i R x J xh Jh, Relation.ReflTransGen (A2Step L) (A2Init n) (.done i R x J xh Jh) →
        (J = maxSupp L ∧ x ∈ L ∧ x ∈ nonneg n ∧ ∀ j ∈ J, 0 < x j) ∧
          (Jh = maxSupp Lᗮ ∧ xh ∈ Lᗮ ∧ xh ∈ nonneg n ∧ ∀ j ∈ Jh, 0 < xh j)) := by sorry

end ProjRescale.MaxSupport
