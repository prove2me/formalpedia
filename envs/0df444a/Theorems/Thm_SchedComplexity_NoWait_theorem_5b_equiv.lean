-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_theorem_5b_equiv
-- name    : SchedComplexity.NoWait.theorem_5b_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:16:10.663171+00:00
-- url     : https://prove2.me/theorems/9842b57f-f4fd-45d5-bf29-d11af6b231b4
-- title:
--   Theorem 5(b) — G has a Hamilton path iff the instance of (a) has Σ_j C_j ≤ ½n(n − 1)(μ + 2λ) + nmμ
-- statement:
--   With the same graph, assignment $\iota$, parameters $\lambda\ge1$, $\mu\ge2\lambda+3$, and the instance "constructed as in (a)", now read as an instance of $n|m|F,\textit{no wait},w_j=1|\sum w_jC_j$: $G$ has a Hamilton path if and only if some feasible schedule has
--   $$\sum_j C_j\le\tfrac12 n(n-1)(\mu+2\lambda)+nm\mu.$$
--
--   This is the correctness of the reduction in Theorem 5(b).
--
--   **Formalization Note** The threshold is compared in $\mathbb Q$ exactly as printed; since $n(n-1)$ is even it is an integer. For $n=2$ the hypothesis on $\iota$ cannot be met.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 25, proof of Theorem 5(b)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- Theorem 5(b), the equivalence (p. 25): for the instance constructed as in (a), with an
admissible `ι`, `λ ≥ 1` and `μ ≥ 2λ + 3`, the graph has a Hamilton path iff some feasible
no-wait schedule has `Σ_j C_j ≤ ½ n(n − 1)(μ + 2λ) + nmμ` (compared in `ℚ`, as printed). -/
theorem theorem_5b_equiv {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    HasHamiltonPath adj ↔
      ∃ B, IsNoWaitSchedule (procTimes adj ι lam mu) B ∧
        ((∑ ℓ, completion (procTimes adj ι lam mu) B ℓ : ℕ) : ℚ) ≤
          (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((mu : ℚ) + 2 * lam) +
            (n : ℚ) * (numMachines n : ℚ) * mu := by sorry

end SchedComplexity.NoWait
