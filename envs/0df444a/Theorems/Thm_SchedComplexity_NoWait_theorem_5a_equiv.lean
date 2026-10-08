-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_theorem_5a_equiv
-- name    : SchedComplexity.NoWait.theorem_5a_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:14:47.561509+00:00
-- url     : https://prove2.me/theorems/9be5728a-7560-4a02-86b9-ac43038d381e
-- title:
--   Theorem 5(a) — G has a Hamilton path iff the no-wait flow shop has C_max ≤ (n − 1)(μ + 2λ) + mμ
-- statement:
--   Let $G=(V,A)$ be a directed graph with $n=|V|$, $m=n(n-1)+2$, $\iota$ an admissible assignment, and $\lambda\ge1$, $\mu\ge2\lambda+3$. Consider the $n|m|F,\textit{no wait}|C_{\max}$ instance of the construction of Theorem 5. Then $G$ has a Hamilton path if and only if this instance has a feasible schedule with
--   $$C_{\max}\le(n-1)(\mu+2\lambda)+m\mu.$$
--
--   This is the correctness of the reduction in Theorem 5(a).
--
--   **Formalization Note** $C_{\max}\le y$ is stated as $C_\ell\le y$ for every job. The threshold is computed in $\mathbb N$; at $n=0$, $(n-1)$ truncates to $0$, and both sides hold there. For $n=2$ the hypothesis on $\iota$ cannot be met, so the statement says nothing about $n=2$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 25, proof of Theorem 5(a)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- Theorem 5(a), the equivalence (p. 25): for an admissible `ι`, `λ ≥ 1` and `μ ≥ 2λ + 3`, the
directed graph `adj` on `n` vertices has a Hamilton path iff the constructed
`n|m|F,no wait|C_max` instance (`m = n(n−1)+2`) has a feasible schedule with
`C_max ≤ (n − 1)(μ + 2λ) + mμ`. -/
theorem theorem_5a_equiv {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    HasHamiltonPath adj ↔
      ∃ B, IsNoWaitSchedule (procTimes adj ι lam mu) B ∧
        ∀ ℓ, completion (procTimes adj ι lam mu) B ℓ ≤
          (n - 1) * (mu + 2 * lam) + numMachines n * mu := by sorry

end SchedComplexity.NoWait
