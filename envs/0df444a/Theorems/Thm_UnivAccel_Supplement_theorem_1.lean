-- Prove2me | Theorems.Thm_UnivAccel_Supplement_theorem_1
-- name    : UnivAccel.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:59:06.23148+00:00
-- url     : https://prove2.me/theorems/b84d9f84-6199-46e4-8673-f0796b353141
-- title:
--   Theorem 1 — implicit Euler+GD in $O(\sqrt\kappa\log\frac{2\Delta}{\varepsilon}\log\frac{2\kappa\Delta}{\varepsilon})$, Nesterov's AGD in $O(\sqrt\kappa\log\frac{2\Delta}{\varepsilon})$ queries
-- statement:
--   **Theorem 1 (Accelerated gradient descent).** There is an absolute constant $C > 0$ with the following property. Let $0 < \mu \le L$, $\kappa = L/\mu$, and $0 < \varepsilon < \Delta$. Then:
--
--   1. **(implicit Euler with gradient descent)** there are an outer count $N$ and an inner count $T$, depending only on $(L, \mu, \Delta, \varepsilon)$, with
--   $$
--   N\cdot T \le C\sqrt\kappa\,\log\frac{2\Delta}{\varepsilon}\,\log\frac{2\kappa\Delta}{\varepsilon},
--   $$
--   such that for every dimension $n$, every $L$-smooth (differentiable with $L$-Lipschitz gradient) and $\mu$-strongly convex $f : \mathbb R^n \to \mathbb R$ with minimizer $x^*$, and every $x_0$ with $f(x_0) - f(x^*) \le \Delta$, the implicit Euler method (13) with each step solved by $T$ gradient-descent iterations (§4.1), run for $N$ outer steps from $x_0$ at rest, outputs $x_N$ with $f(x_N) - f(x^*) \le \varepsilon$, using $N\cdot T$ gradient queries;
--   2. **(lookahead = Nesterov's AGD)** there is a count $N \le C\sqrt\kappa\log(2\Delta/\varepsilon)$, depending only on $(L, \mu, \Delta, \varepsilon)$, such that for every such $n$, $f$, $x^*$, $x_0$ the lookahead method (27) with the gradient step and $h = 1/\sqrt L$ (§5.2), run for $N$ steps from $x_0$ at rest, outputs $\bar x_N$ with $f(\bar x_N) - f(x^*) \le \varepsilon$, using $N$ gradient queries.
--
--   Clause (b) is the optimal accelerated rate for smooth strongly convex minimization; clause (a) matches it up to the logarithmic cost of the inner solves. Both are derived from implicit Euler discretizations of the heavy-ball ODE and certified by the potential $H = f(x) + \tfrac12\|v + \sqrt\mu\,x\|^2$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; strong convexity is Mathlib's `StrongConvexOn Set.univ μ f` (the $\frac\mu2\|\cdot\|^2$ convention); logarithms are natural. The paper's analysis also counts nothing but gradient evaluations, and so does the statement.
--
--   Differences from the source:
--   - reading: "O(·) gradient queries" for a method whose inner accuracy is "δ polynomially small in µ and ε/H0" (p.12) → one absolute constant C, and the counts N, T (resp. N) chosen from (L, μ, Δ, ε) only, before n, f, x0, x*; reason: a method chooses its budget from the known data, and H0 ≤ 2Δ/L at a zero-velocity start, so the paper's δ is a function of these data
--   - reading: inner gradient descent with unspecified starting point → warm start y₀ = x_{1/2}; reason: the page does not fix it, and the prediction is the point Q is centred at
--   - reading: methods started "from x0" → started at rest (v₀ = 0, w̄₀ = √μ x0); reason: the paper's potential analysis starts at zero velocity (§3.4, p.10; §5.4), which gives H0 ≤ 2Δ
--   - encoding: methods analysed for 1-smooth f with x* = 0 → stated for L-smooth f in original coordinates (f/L, μ/L at h = 1 for (a); h = 1/√L for (b)); reason: the paper's own rescaling (pp.12, 17), and both iterations are translation covariant
--   - encoding: "L-smooth and µ-strongly convex" → Differentiable ℝ f, ‖∇f x − ∇f y‖ ≤ L‖x − y‖, StrongConvexOn univ μ f, 0 < μ ≤ L; reason: μ ≤ L follows from the other hypotheses for n ≥ 1 and is stated because the counts are chosen before n
--   - encoding: "finds x" → the last iterate after the counted steps; reason: the method's output
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), Theorem 1, p.5; methods §4.1 pp.10–12 and §5.2 pp.18–19

import Mathlib
import Definitions.Def_UnivAccel_Supplement_iegdRun
import Definitions.Def_UnivAccel_Supplement_agdRun

namespace UnivAccel.Supplement

/-- Theorem 1 (Accelerated gradient descent), p.5 (Adil–Kyng, *Universal Acceleration: New
Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)).
Let `f` be `L`-smooth and `μ`-strongly convex with minimizer `x*`, let `κ = L/μ`, and let
`f(x0) − f(x*) ≤ Δ`. For every `ε ∈ (0, Δ)`, the implicit Euler method (13), with each step solved
by gradient descent (Section 4.1), finds `x` with `f(x) − f(x*) ≤ ε` using
`O(√κ log 2Δ/ε · log 2κΔ/ε)` gradient queries. The lookahead method (27), which is exactly
Nesterov's accelerated gradient descent (Section 5.2), does so using `O(√κ log 2Δ/ε)` gradient
queries.

**Formalization Note** One absolute constant `C > 0` is quantified first. The iteration counts (the
outer count `N` and the inner gradient-descent count `T` in clause (a), the step count `N` in
clause (b)) are chosen from `(L, μ, Δ, ε)` only, before the dimension, `f`, `x0` and `x*`. Clause (a)
uses `N·T` gradient queries (`iegdRun`), clause (b) uses `N` (`agdRun`); each outputs its last
iterate. `L`-smoothness is `Differentiable ℝ f` with an `L`-Lipschitz `gradient f`; strong
convexity is Mathlib's `StrongConvexOn Set.univ μ f` (the `μ/2‖·‖²` convention). `μ ≤ L` is stated
because the counts are chosen before `n` (it follows from the other hypotheses for `n ≥ 1`). -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (L μ Δ ε : ℝ), 0 < μ → μ ≤ L → 0 < ε → ε < Δ →
      (∃ N T : ℕ,
        ((N * T : ℕ) : ℝ) ≤
          C * Real.sqrt (L / μ) * Real.log (2 * Δ / ε) * Real.log (2 * (L / μ) * Δ / ε) ∧
        ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (xstar x0 : EuclideanSpace ℝ (Fin n)),
          Differentiable ℝ f → (∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) →
          StrongConvexOn Set.univ μ f → (∀ y, f xstar ≤ f y) → f x0 - f xstar ≤ Δ →
          f (iegdRun f L μ T x0 N).1 - f xstar ≤ ε) ∧
      (∃ N : ℕ, (N : ℝ) ≤ C * Real.sqrt (L / μ) * Real.log (2 * Δ / ε) ∧
        ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (xstar x0 : EuclideanSpace ℝ (Fin n)),
          Differentiable ℝ f → (∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) →
          StrongConvexOn Set.univ μ f → (∀ y, f xstar ≤ f y) → f x0 - f xstar ≤ Δ →
          f (agdRun f L μ x0 N).1 - f xstar ≤ ε) := by sorry

end UnivAccel.Supplement
