-- Prove2me | Theorems.Thm_SmaleNinth_khachiyan_ellipsoid_decides
-- name    : SmaleNinth.khachiyan_ellipsoid_decides
-- status  : Proved
-- author  : @ORdos
-- created : 2026-09-06T15:26:45.957873+00:00
-- url     : https://prove2.me/theorems/970f506f-2b47-4e74-b66b-6a249171e70e
-- title:
--   Khachiyan's theorem: LP feasibility in polynomially many ellipsoid iterations
-- statement:
--   This is the statement that linear feasibility with integer data is decided in polynomially many ellipsoid iterations — the 1979 result that placed linear programming in polynomial time.
--
--   **The iteration.** An **admissible run** of the ellipsoid method on a system $Cx \ge d$ is a sequence of centres $x_t \in \mathbb{R}^n$ and shape matrices $D_t$ such that, at every time $t$ at which the current centre is infeasible, *some* violated row $c_i^{\mathsf T} x_t < d_i$ is selected and the successor is produced by the standard update
--
--   $$x_{t+1} = x_t + \frac{1}{n+1}\cdot\frac{D_t c_i}{\sqrt{c_i^{\mathsf T} D_t c_i}}, \qquad D_{t+1} = \frac{n^2}{n^2-1}\left(D_t - \frac{2}{n+1}\cdot\frac{D_t c_i c_i^{\mathsf T} D_t}{c_i^{\mathsf T} D_t c_i}\right),$$
--
--   the smallest ellipsoid containing the half of the current one that still contains the feasible set. Nothing constrains which violated row is chosen, so the theorem holds for **every** rule for selecting violated constraints; and nothing is constrained once a centre is feasible, since the algorithm has then answered.
--
--   **The assertion.** Let $n \ge 2$ and $U \ge 1$, let $A \in \mathbb{Z}^{m\times n}$ and $b \in \mathbb{Z}^m$ have entries bounded by $U$ in absolute value, and consider any admissible run on the perturbed-and-boxed system $\widehat P$ started at $x_0 = 0$ with $D_0 = r^2 I$, the ball of enclosing radius $r = (n+1)(n!\,U^n+1)$. Then
--
--   $$\bigl(\exists\, t \le t^{*} :\ x_t \in \widehat P\bigr) \qquad\Longleftrightarrow\qquad \{x \in \mathbb{R}^n \mid Ax \ge b\} \ne \emptyset ,$$
--
--   and the budget is polynomially bounded,
--
--   $$t^{*} \;\le\; 10^{6}\,(n+2)^{4}\,\bigl(\log_2 U + n + 2\bigr).$$
--
--   **Reading the equivalence.** The two sides concern different sets: the run is observed on the perturbed-and-boxed system, while the conclusion is about the *original* system. That the one decides the other is the content of the perturbation bounds. Running the budget to exhaustion without a feasible centre is therefore a proof of infeasibility, not merely a failure to find a point.
--
--   **Where the hypotheses bite.** The restriction $n \ge 2$ comes from the factor $n^2/(n^2-1)$ in the update, and $U \ge 1$ keeps the constants nondegenerate. The numerical bound uses the integer base-$2$ logarithm, and its constant is deliberately generous — only the polynomial order in $n$ and $\log U$ is load-bearing.
--
--   **What remains open after this.** The count is polynomial in $n$ and in $\log U$, the bit length of the data. Removing that dependence on $U$ — a bound in $m$ and $n$ alone, valid for arbitrary real data — is exactly the mission's goal, and no known method achieves it.
-- source:
--   L.G. Khachiyan, A polynomial algorithm in linear programming, Soviet Math. Doklady 20 (1979) 191-194. Textbook: B. Korte, J. Vygen, Combinatorial Optimization, 6th ed., Section 4.5 (Khachiyan's theorem); ellipsoid iteration harness: Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Chapter 8 (platform mission Introduction to Linear Optimization XI).

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_LinearOptimization_EllipsoidMethod
import Definitions.Def_SmaleNinth_Khachiyan

/-!
Khachiyan's theorem in iteration form: the ellipsoid method decides the
feasibility of an integer linear system within an explicitly polynomial
number of iterations.

Source: L.G. Khachiyan, *A polynomial algorithm in linear programming*,
Soviet Math. Doklady 20 (1979) 191–194 — the result that linear programming
feasibility with rational data is decidable in polynomial time. Textbook
treatment: B. Korte, J. Vygen, *Combinatorial Optimization*, 6th ed.,
§4.4–4.5 (Khachiyan's theorem); the ellipsoid iteration itself is the
platform's `LinearOptimization` development of Bertsimas–Tsitsiklis,
*Introduction to Linear Optimization*, Chapter 8.

Every admissible run of the ellipsoid method (any rule for choosing violated
constraints) on the perturbed-and-boxed system, started from the ball of
radius `khachiyanRadius n U`, decides within `khachiyanIterations n U`
iterations whether `Ax ≥ b` is solvable: some center lands in the
perturbed-and-boxed polyhedron iff the original system is solvable. The
iteration budget is bounded by an explicit polynomial in `n` and `log₂ U` —
this, not any particular constant, is the content of "polynomially many
iterations". (The generous constant `10⁶·(n+2)⁴·(log₂ U + n + 2)` absorbs
the crude Cramer–Hadamard estimates fixed in
`Definitions.Def_SmaleNinth_Khachiyan`.)
-/

open Matrix LinearOptimization

/-- **Khachiyan's theorem, iteration form** (Khachiyan 1979; Korte–Vygen
§4.5). For an integer system `Ax ≥ b` in `n ≥ 2` variables with entries
bounded by `U ≥ 1`: every admissible ellipsoid run on the
perturbed-and-boxed system, started at the origin with the ball of radius
`khachiyanRadius n U`, hits the perturbed-and-boxed polyhedron with some
center within `khachiyanIterations n U` iterations **iff** `Ax ≥ b` has a
real solution — and the iteration budget is polynomially bounded:
`khachiyanIterations n U ≤ 10⁶·(n+2)⁴·(log₂ U + n + 2)`. -/

theorem SmaleNinth.khachiyan_ellipsoid_decides {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (hn : 2 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (x : ℕ → Fin n → ℝ) (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hx0 : x 0 = 0)
    (hD0 : D 0 = (khachiyanRadius n U) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hrun : IsEllipsoidRun (khachiyanSystemA A) (khachiyanSystemb n U b)
      x D (khachiyanIterations n U)) :
    ((∃ t ≤ khachiyanIterations n U,
        x t ∈ polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b)) ↔
      (polyhedron (A.map (Int.cast : ℤ → ℝ))
        (fun i => (b i : ℝ))).Nonempty) ∧
    khachiyanIterations n U ≤
      10 ^ 6 * (n + 2) ^ 4 * (Nat.log 2 U + n + 2) := by sorry
