-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_theorem_3_7
-- name    : UniformPrecSched.Makespan.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:33:00.585427+00:00
-- url     : https://prove2.me/theorems/da5cd3d0-f420-413e-8700-e8a7e1824e7a
-- title:
--   Theorem 3.7 — a min{K + 2√K + 1, 1.89 log m + O(√log m)}-approximation algorithm for Q|prec|C_max
-- statement:
--   There is an absolute constant $c$ such that the following holds. Let $I$ be an instance of $Q|prec|C_{\max}$ with $m \ge 2$ machines and $K$ distinct machine speeds, and consider the algorithm that returns the shorter of two schedules:
--
--   1. **(A)** take an optimal solution of LP for $I$, an assignment computed from it by the assignment algorithm with $B_j = \{k : p_j/\bar s_k > (\sqrt K + 1)\bar p_j\}$, and a schedule $\sigma_A$ produced by the speed-based list scheduling algorithm for that assignment;
--   2. **(B)** round the speeds with $\alpha = \log_2 m$ and $\beta = e$ (drop machines slower than $\bar s_1/(\alpha m)$, round every other speed down to the power $\bar s_1 e^{-k}$ just below it), obtaining an instance $I'$ with $K'$ distinct speeds; do (A) on $I'$ with threshold $\sqrt{K'} + 1$, obtaining a schedule $\sigma_B'$ of $I'$; and read $\sigma_B'$ on the original machines with the same start times, obtaining a schedule $\sigma_B$ of $I$.
--
--   Then for every feasible schedule $\sigma^*$ of $I$,
--   $$\min\{C_{\max}(\sigma_A), C_{\max}(\sigma_B)\} \le \min\bigl\{K + 2\sqrt K + 1,\ 1.89\log_2 m + c\sqrt{\log_2 m}\bigr\}\, C_{\max}(\sigma^*).$$
--   That is, if $K$ is the number of different machine speeds, there is a $\min\{K + 2\sqrt K + 1, 1.89\log m + O(\sqrt{\log m})\}$-approximation algorithm for $Q|prec|C_{\max}$.
--
--   This improved the best known guarantee for scheduling precedence-constrained jobs on uniformly related machines from $O(\sqrt m)$ to $O(\log m)$.
--
--   **Formalization Note** Every choice the algorithm leaves open is universally quantified: the optimal LP solutions, ties in the assignment, the list order and machine order of list scheduling (through the speed-based list schedule predicate), and the schedule $\sigma_B$ of $I$ with the same machines and start times as $\sigma_B'$. Their existence is the content of the milestones on LP optima, assignments, list schedules and rounded schedules. The comparator is every feasible schedule of $I$. $\log m$ is $\log_2 m$; $m \ge 2$ is assumed because the bound is asymptotic in $m$ and $\log_2 1 = 0$. The constant $c$ is absolute: it is chosen before $n$, $m$ and the instance. Polynomial running time is not formalized.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 10, Theorem 3.7

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP
import Definitions.Def_UniformPrecSched_Makespan_Rounding

namespace UniformPrecSched.Makespan

/-- Theorem 3.7 (p. 10): the algorithm that returns the shorter of the two schedules
(A) the assignment algorithm (from an optimal solution of `LP`, threshold `√K + 1`) combined with
    the speed-based list scheduling algorithm, on the instance itself, and
(B) the same algorithm on the instance with rounded speeds (`α = log₂ m`, `β = e`; threshold
    `√K' + 1` with `K'` the number of rounded speeds), read back on the original machines,
is a `min{K + 2√K + 1, 1.89 log₂ m + O(√(log₂ m))}`-approximation algorithm for `Q|prec|C_max`:
there is one absolute constant `c` such that, for every instance with `m ≥ 2` machines, the
returned schedule has length at most `min{K + 2√K + 1, 1.89 log₂ m + c √(log₂ m)}` times the
length of any feasible schedule. -/
theorem theorem_3_7 :
    ∃ c : ℝ, ∀ (n m : ℕ) (I : Instance n m) (hm : 2 ≤ m),
      ∀ (x : Fin (numSpeeds I) → Fin n → ℝ) (C : Fin n → ℝ) (D : ℝ), LPOptimal I x C D →
      ∀ kA : Assignment I, IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) kA →
      ∀ σA : Schedule I, IsSpeedListSchedule I kA σA →
      ∀ (x' : Fin (numSpeeds (logRoundInstance I hm)) → Fin n → ℝ) (C' : Fin n → ℝ) (D' : ℝ),
        LPOptimal (logRoundInstance I hm) x' C' D' →
      ∀ kB : Assignment (logRoundInstance I hm),
        IsLPAssignment (logRoundInstance I hm) x'
          (Real.sqrt (numSpeeds (logRoundInstance I hm)) + 1) kB →
      ∀ σB' : Schedule (logRoundInstance I hm), IsSpeedListSchedule (logRoundInstance I hm) kB σB' →
      ∀ σB : Schedule I,
        (∀ j, σB.μ j = keptEmb I (Real.logb 2 m) (σB'.μ j) ∧ σB.S j = σB'.S j) →
      ∀ σstar : Schedule I,
        min σA.makespan σB.makespan ≤
          min ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1)
              (1.89 * Real.logb 2 m + c * Real.sqrt (Real.logb 2 m)) * σstar.makespan := by sorry

end UniformPrecSched.Makespan
