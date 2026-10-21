-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_theorem_1
-- name    : StochLoadBal.Makespan.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:13.339211+00:00
-- url     : https://prove2.me/theorems/c8a1f837-043b-4661-b689-2f6cd59dab38
-- title:
--   Theorem 1, pinned — the effective-size LP and its rounding give an O(1)-approximation to the minimum expected makespan on unrelated machines
-- statement:
--   There is an absolute constant $c_0>0$ such that the following holds for every instance of stochastic load balancing on $m\ge1$ unrelated machines (sizes $X_{ij}\ge0$, measurable and integrable, with the jobs independent) and every scale $M>0$. Write $X/M$ for the instance with sizes $X_{ij}/M$.
--
--   1. **(Lower bound.)** If some assignment has expected makespan at most $c_0M$, then the LP (5)–(9) for $X/M$ with $b=17$ is feasible.
--   2. **(Rounding exists.)** For every $b\ge0$ and every feasible solution $y$ of the LP (5)–(9) for $X/M$ with parameter $b$, there is an assignment with properties (13)–(14) for $X/M$, $b$ and $y$.
--   3. **(Upper bound.)** Every such assignment $\sigma$ satisfies
--   $$\mathbb E\Big[\max_{i\in[m]}\sum_{j\in J_i}X_{ij}\Big]\ \le\ (4b+10)\,M .$$
--
--   Together: for $M\ge \mathrm{OPT}/c_0$, where $\mathrm{OPT}$ is the minimum expected makespan, part 1 makes the LP with $b=17$ feasible, part 2 yields an output of the rounding and part 3 bounds its expected makespan by $78M$. With $M=\mathrm{OPT}/c_0$ (found up to a factor $2$ by binary search) this is a $78/c_0$-approximation, which is the content of the paper's Theorem 1: "There is an $O(1)$-approximation algorithm for the problem of finding an assignment to minimize the expected makespan on unrelated machines."
--
--   **Formalization Note** The literal claim "there is an $O(1)$-approximation algorithm" is not formalized as an existential over assignments, which is trivially true; the statement is about the paper's own procedure (LP, class loop, assignments with the Shmoys–Tardos guarantee (13)–(14)), none of which sees the optimum. Running time and the binary search over $M$ are not modelled. The constant $c_0$ replaces the $1$ of Proposition 1 (see the corrected Lemma 5).
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 8, Theorem 1 (also p. 2; proof pp. 9–13)

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Theorem 1 (p. 8), pinned to the paper's procedure. There is an absolute constant `c₀ > 0`
such that for every instance and every scale `M > 0`:
(A) if some assignment has expected makespan at most `c₀ M`, the LP (5)–(9) for the scaled
sizes `X / M` with `b = 17` is feasible;
(B) for every `b ≥ 0` and every feasible solution `y` of that LP, the rounding has an output
(an assignment with (13)–(14));
(C) every such output has expected makespan at most `(4b + 10) M`. -/
theorem theorem_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (m n : ℕ), 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin m → Fin n → Ω → ℝ),
        (∀ i j, Measurable (X i j)) → (∀ i j ω, 0 ≤ X i j ω) →
        (∀ i j, Integrable (X i j) P) → iIndepFun (fun j ω i => X i j ω) P →
        ∀ M : ℝ, 0 < M →
          ((∃ σ : Fin n → Fin m, expMakespan P X σ ≤ c₀ * M) →
              ∃ y : Fin m → Fin n → ℝ, LPFeasible P (scale M X) 17 y) ∧
          ∀ b : ℝ, 0 ≤ b → ∀ y : Fin m → Fin n → ℝ, LPFeasible P (scale M X) b y →
            (∃ σ : Fin n → Fin m, IsRoundingOutput P (scale M X) b y σ) ∧
            ∀ σ : Fin n → Fin m, IsRoundingOutput P (scale M X) b y σ →
              expMakespan P X σ ≤ (4 * b + 10) * M := by sorry

end StochLoadBal.Makespan
