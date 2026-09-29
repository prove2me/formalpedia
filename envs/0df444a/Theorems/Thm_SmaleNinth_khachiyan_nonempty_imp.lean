-- Prove2me | Theorems.Thm_SmaleNinth_khachiyan_nonempty_imp
-- name    : SmaleNinth.khachiyan_nonempty_imp
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T01:12:16.216259+00:00
-- url     : https://prove2.me/theorems/8b2eaf9d-c6d7-4823-a9a1-22faf3f72a5a
-- title:
--   Perturbing cannot create feasibility (the Farkas direction)
-- statement:
--   **Perturbing cannot create feasibility: the Farkas direction.**
--
--   Let $Ax \ge b$ be an integer system in $n\ge1$ variables with all entries bounded by $U\ge1$, and let $\varepsilon = 1/\bigl(2(n+1)(n+1)!\,U^{n+1}\bigr)$, $M = n!\,U^{n}+1$. If the relaxed and boxed system
--   $$Ax \ge b - \varepsilon\mathbf 1,\qquad -M\mathbf 1 \le x \le M\mathbf 1$$
--   has a solution, then so does the original $Ax \ge b$.
--
--   This is the non-obvious half of the feasibility equivalence. The other half — a feasible integer system stays feasible after relaxing and boxing — is proved in the companion reduction, and is easy once one knows the system has a *small* solution. This direction is where the specific value of $\varepsilon$ earns its keep: relaxing every right-hand side makes the system strictly easier, and the claim is that with this $\varepsilon$ it cannot become solvable when it was not.
--
--   **The argument.** Suppose $Ax\ge b$ is infeasible. By Farkas' lemma — available on the platform as `LinearOptimization.farkas_lemma` — there is $y \ge 0$ with
--   $$y^{\mathsf T}A = 0, \qquad y^{\mathsf T}b > 0 .$$
--   Such a certificate can be taken to be a *basic* solution of the system defining it, so its nonzero entries are given by Cramer's rule on a nonsingular square subsystem with integer data bounded by $U$. Two consequences follow from the determinant bounds already on the platform, `SmaleNinth.abs_det_le_factorial_mul_pow` and `SmaleNinth.cramer_solution_bound`: after scaling the certificate so that its entries are integers, $y^{\mathsf T}b \ge 1$, while $\|y\|_1$ is bounded by an explicit quantity of the same shape as $1/\varepsilon$.
--
--   Now suppose $x$ satisfies the relaxed system. Multiplying by $y\ge0$ and using $y^{\mathsf T}A = 0$,
--   $$0 \;=\; y^{\mathsf T}(Ax) \;\ge\; y^{\mathsf T}b - \varepsilon\,\|y\|_1 ,$$
--   so $y^{\mathsf T}b \le \varepsilon\|y\|_1$. The constant $\varepsilon$ is chosen precisely so that $\varepsilon\|y\|_1 < 1 \le y^{\mathsf T}b$, a contradiction. Hence no such $x$ exists and the relaxed system is infeasible too.
--
--   The box constraints play no role in this direction; they matter only for the converse, where they must be wide enough to contain a solution, which is what $M = n!\,U^{n}+1$ guarantees.
-- source:
--   L. G. Khachiyan, A polynomial algorithm in linear programming, Soviet Math. Doklady 20 (1979) 191-194; B. Korte, J. Vygen, Combinatorial Optimization, 6th ed., Springer 2018, Sections 4.4-4.5; D. Bertsimas, J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Theorem 4.6 (Farkas) and Section 8.4. One direction of SmaleNinth.khachiyan_feasibility_equiv.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_Khachiyan

open Matrix LinearOptimization

theorem SmaleNinth.khachiyan_nonempty_imp {m n : ℕ} (U : ℕ) (hU : 1 ≤ U) (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    (polyhedron (SmaleNinth.khachiyanSystemA A)
        (SmaleNinth.khachiyanSystemb n U b)).Nonempty →
      (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty := by sorry
