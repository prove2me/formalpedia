-- Prove2me | Theorems.Thm_QueueingFundamentals_AdvMarkov_partial_batch_steady_state
-- name    : QueueingFundamentals.AdvMarkov.partial_batch_steady_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:39:34.071728+00:00
-- url     : https://prove2.me/theorems/40ef50dc-289e-4a4f-9570-469c5ca816aa
-- title:
--   Eq. (3.9): the geometric steady-state solution of the partial-batch M/M^[K]/1 queue
-- statement:
--   Consider the partial-batch bulk-service queue $M/M^{[K]}/1$ with arrival rate $\lambda > 0$, batch service rate $\mu > 0$ and maximal batch size $K \ge 1$, and assume $\lambda < K\mu$. Then:
--
--   1. the characteristic equation of (3.8),
--   $$\mu r^{K+1} - (\lambda+\mu)r + \lambda = 0,$$
--   has exactly one root $r_0$ in the open interval $(0,1)$;
--   2. for this root, the sequence
--   $$p_n = (1 - r_0)\,r_0^n \qquad (n \ge 0) \qquad (3.9)$$
--   is a probability distribution solving the balance equations (3.7), and every probability solution of (3.7) equals it.
--
--   The steady state thus has the same geometric form as that of the $M/M/1$ queue, with $r_0$ in place of $\rho$; for $K = 1$, $r_0 = \lambda/\mu$.
--
--   **Formalization Note** The book invokes Rouché's theorem to assert that exactly one root lies in $(0,1)$ without naming the condition; $\lambda < K\mu$ (the server's capacity exceeds the arrival rate) is exactly the condition under which such a root exists, and is stated as a hypothesis. Both the existence and the uniqueness of the root are part of the statement.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.124, Eqs. (3.7), (3.8), (3.9)

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_BulkService

namespace QueueingFundamentals.AdvMarkov

/-- Eq. (3.9), p.124: for the partial-batch `M/M^[K]/1` queue with `λ < Kμ`, the characteristic
equation `μr^{K+1} − (λ + μ)r + λ = 0` of (3.8) has exactly one root `r_0` in `(0, 1)`, and the
steady-state solution of (3.7) is `p_n = (1 − r_0)r_0ⁿ` (`n ≥ 0`): this sequence is a probability
solution of (3.7), and every probability solution of (3.7) equals it. -/
theorem partial_batch_steady_state (lam mu : ℝ) (K : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hK : 1 ≤ K) (hstab : lam < (K : ℝ) * mu) :
    (∃! r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 ∧ mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0) ∧
      ∀ r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 → mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0 →
        IsPartialBatchSteadyState lam mu K (fun n : ℕ => (1 - r0) * r0 ^ n) ∧
          ∀ p : ℕ → ℝ, IsPartialBatchSteadyState lam mu K p →
            ∀ n : ℕ, p n = (1 - r0) * r0 ^ n := by sorry

end QueueingFundamentals.AdvMarkov
