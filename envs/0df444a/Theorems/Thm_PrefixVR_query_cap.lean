-- Prove2me | Theorems.Thm_PrefixVR_query_cap
-- name    : PrefixVR.query_cap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:39.135848+00:00
-- url     : https://prove2.me/theorems/331e359a-9af9-47c5-9447-3d375e8f5b6d
-- title:
--   §3.4 — at most five queries per update, each at $x_t$ or $x_{t+1}$
-- statement:
--   Run Algorithm 1 with horizon $T$, any stepsize $\eta$ and initial point $x_1$. Then
--
--   1. the initialization makes exactly $n$ component-gradient queries, all at $x_1$;
--   2. on every outcome of the draws, every update $1\le t\le T$ makes at most five component-gradient queries, and every one of them is made at $x_t$ or at $x_{t+1}$.
--
--   (An ordinary update with a nonempty proper prefix makes two queries for the sampled prefix difference, one for the newly inserted component and two for the active recursion; at $r=1$ no prefix difference is needed, and at the cycle boundary $r=n$ the active recursion is omitted.) The cap holds at every update, not only in expectation.
--
--   **Formalization Note** A query is an entry $(i,x)$ of the log written by the logging oracle; the algorithm reaches the gradients only through that oracle. Repeated queries of the same pair count separately (p.4).
--
--   Differences from the source:
--   - generalization: the component gradients ∇fᵢ and η > 0 → arbitrary maps g i and any real η; reason: the count does not depend on them
--   - encoding: a component-gradient query → an entry (i, x) of the oracle's log; reason: each oracle call appends exactly one entry
--   - encoding: components i ∈ [n] = {1, …, n} → Fin n, paper index i is i − 1, with NeZero n; reason: Lean convention; n ≥ 1 is the paper's standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §3.4, p.7 (PDF p.7); App. C, "Query and memory counts", p.16

import Mathlib
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run

namespace PrefixVR

/-- **The per-update query cap.** Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…),
§3.4, p.7: "Initialization costs n component-gradient queries at x₁. … Thus the count is at most
five, including the cycle boundary … Every post-initialization query is made at x_t or x_{t+1}";
App. C, "Query and memory counts", p.16.

For Algorithm 1 with horizon `T`, any maps `g`, stepsize `η`, initial point `x₁`: the
initialization makes exactly `n` queries, all at `x₁`; on every outcome `ω`, every update
`1 ≤ t ≤ T` makes at most five queries, each at `x_t` or `x_{t+1}`.

**Formalization Note.** A query is an entry `(i, x)` of the log written by the logging oracle
(`logOracle`); the algorithm reaches the gradients only through the oracle (`init` and `step` are
generic in the monad). Repeated queries of the same `(i, x)` count separately (p.4). -/
theorem query_cap {n d : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℝ)
    (x₁ : EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    (initLog g x₁).length = n ∧ (∀ q ∈ initLog g x₁, q.2 = x₁) ∧
    ∀ ω : Sample n T, ∀ t : ℕ, 1 ≤ t → t ≤ T →
      (updateLog g η x₁ ω t).length ≤ 5 ∧
      ∀ q ∈ updateLog g η x₁ ω t, q.2 = xIter g η x₁ ω t ∨ q.2 = xIter g η x₁ ω (t + 1) := by sorry

end PrefixVR
