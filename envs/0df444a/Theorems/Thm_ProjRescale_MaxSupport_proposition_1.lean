-- Prove2me | Theorems.Thm_ProjRescale_MaxSupport_proposition_1
-- name    : ProjRescale.MaxSupport.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:39.854004+00:00
-- url     : https://prove2.me/theorems/0eb8b014-4864-4e7c-816e-8003a96630a8
-- title:
--   Proposition 1, p. 6 — Algorithm 1 halts with a partial-support solution, J = J(L) when σ ≤ σ(L) (corrected: ≤ n(⌊log₂(1/σ)⌋ + 1) rescalings; J_σ(L) ⊆ J only for σ ≤ σ(L))
-- statement:
--   Let $n \ge 1$, let $L \subseteq \mathbb R^n$ be a linear subspace and let $\sigma \in (0,1)$. Consider Algorithm 1 (Partial support) on input $(L, \sigma)$, with any admissible behaviour of the basic procedure and any choice of the maximizer $i$ in step 5. Then:
--
--   1. **(progress)** every non-halted state reachable by the algorithm has an admissible next step;
--   2. **(termination)** there is no infinite execution;
--   3. **(rescaling count)** every execution performs at most
--   $$n\big(\lfloor \log_2(1/\sigma) \rfloor + 1\big)$$
--   rescaling steps;
--   4. **(partial support)** whenever the algorithm halts with output $(x, J)$, we have $x \in L \cap \mathbb R^n_+$, $x_j > 0$ for every $j \in J$, and $J \subseteq J(L)$;
--   5. **(maximum support for a small guess)** if $\sigma \le \sigma(L)$, then every output $(x,J)$ has $J = J(L)$, and the number $r$ of rescaling steps of that execution satisfies
--   $$r \le \sum_{i \in J(L)} \big\lceil \log_2(1/\sigma_i(L)) \big\rceil + \big(n - |J(L)|\big)\big(\lfloor \log_2(1/\sigma)\rfloor + 1\big).$$
--
--   This is the analysis of Algorithm 1 that Theorem 1 runs twice in each main iteration of Algorithm 2.
--
--   **Formalization Note** Algorithm 1 is the transition relation `A1Step L σ` started at `A1Init n` ($D = I$, $J = \{1,\dots,n\}$); every statement quantifies over all executions. The counter `rescalings` of a state is the number of rescaling steps performed so far; clause 3 bounds it at every reachable state. $\lfloor\cdot\rfloor$ and $\lceil\cdot\rceil$ are `Nat.floor` and `Nat.ceil`, whose arguments here are $\ge 0$.
--
--   Differences from the source:
--   - correction: the right-hand side of (5), $n\lceil\log_2(1/\sigma)\rceil$ → $n(\lfloor\log_2(1/\sigma)\rfloor + 1)$; reason: an index is trimmed once $D_{ii} = 2^t > 1/\sigma$, i.e. after $\lfloor\log_2(1/\sigma)\rfloor + 1$ rescalings; counterexample $n = 1$, $L = \{0\}$, $\sigma = 1/2$: $P = 0$ forces $z = e_1$ twice ($D_{11}$: $1 \to 2 \to 4 > 2$), 2 rescaling steps, while (5) gives $1$.
--   - correction: "for some $J_\sigma(L) \subseteq J \subseteq J(L)$ in at most $\sum_{i\in J_\sigma(L)}\lceil\log_2(1/\sigma_i(L))\rceil + (n-|J_\sigma(L)|)\lceil\log_2(1/\sigma)\rceil$ rescaling steps" for every $\sigma \in (0,1)$ → $J \subseteq J(L)$ for every $\sigma$, and $J = J(L)$ with the count $\sum_{i\in J(L)}\lceil\log_2(1/\sigma_i(L))\rceil + (n-|J(L)|)(\lfloor\log_2(1/\sigma)\rfloor+1)$ when $\sigma \le \sigma(L)$ (where $J_\sigma(L) = J(L)$, p. 5); reason: for $\sigma > \sigma(L)$ an index of $J_\sigma(L)$ can be trimmed; counterexample $n = 2$, $L = \mathrm{span}\{(1, 0.1)\}$, $\sigma = 1/2$, $J_\sigma(L) = \{1\}$: the admissible answers $z = e_2, e_2$ trim index 2, then $P = 0$ forces $z = e_1$ twice, and the run ends with $x = 0$, $J = \emptyset \not\supseteq J_\sigma(L)$ after 4 rescaling steps (the printed bound gives 1).
--   - encoding: $n \ge 1$ implicit → hypothesis $0 < n$; reason: for $n = 0$, $\Delta(\{1,\dots,n\}) = \emptyset$ and Algorithm 1 cannot run, so the case is undefined on the page.
--   - encoding: "Algorithm 1 finds … in at most … rescaling steps" → progress, no infinite execution, and the bound at every reachable state of the transition relation, over every admissible answer of the basic procedure; reason: the basic procedure is any procedure satisfying step 3, so the claim is about every execution.
-- source:
--   Peña & Soheili, Projection and rescaling algorithm for finding maximum support solutions to polyhedral conic systems, arXiv:2003.08911v3, p. 6, Proposition 1 (Equation (5)), Algorithm 1

import Mathlib
import Definitions.Def_ProjRescale_MaxSupport_Setting

namespace ProjRescale.MaxSupport

/-- Proposition 1, p. 6, corrected. For `σ ∈ (0, 1)`, every execution of Algorithm 1 on `(L, σ)`
can always continue until it halts, no execution is infinite, every execution performs at most
`n(⌊log₂(1/σ)⌋ + 1)` rescaling steps, and on halting it outputs `x ∈ L ∩ ℝⁿ₊` with `x_J > 0` for
some `J ⊆ J(L)`. If moreover `σ ≤ σ(L)`, then `J = J(L)` and the number of rescaling steps is at most
`∑_{i ∈ J(L)} ⌈log₂(1/σ_i(L))⌉ + (n − |J(L)|)(⌊log₂(1/σ)⌋ + 1)`. -/
theorem proposition_1 (n : ℕ) (hn : 0 < n) (L : Submodule ℝ (E n)) (σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∀ s, Relation.ReflTransGen (A1Step L σ) (A1Init n) s → s.IsRun →
        ∃ s', A1Step L σ s s') ∧
      (¬ ∃ f : ℕ → A1State n, f 0 = A1Init n ∧ ∀ t, A1Step L σ (f t) (f (t + 1))) ∧
      (∀ s, Relation.ReflTransGen (A1Step L σ) (A1Init n) s →
        s.rescalings ≤ n * (⌊Real.logb 2 (1 / σ)⌋₊ + 1)) ∧
      (∀ x J r, A1Halts L σ x J r →
        x ∈ L ∧ x ∈ nonneg n ∧ (∀ j ∈ J, 0 < x j) ∧ J ⊆ maxSupp L) ∧
      (σ ≤ condMeasure L → ∀ x J r, A1Halts L σ x J r →
        J = maxSupp L ∧
          r ≤ ∑ j ∈ maxSupp L, ⌈Real.logb 2 (1 / sigmaI L j)⌉₊ +
            (n - (maxSupp L).card) * (⌊Real.logb 2 (1 / σ)⌋₊ + 1)) := by sorry

end ProjRescale.MaxSupport
