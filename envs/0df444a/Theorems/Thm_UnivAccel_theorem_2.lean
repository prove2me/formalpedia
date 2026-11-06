-- Prove2me | Theorems.Thm_UnivAccel_theorem_2
-- name    : UnivAccel.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:13.548587+00:00
-- url     : https://prove2.me/theorems/ab5d2812-13ee-41ee-825c-4340bc956369
-- title:
--   Theorem 2 — implicit Euler and lookahead, restarted, reach $\varepsilon$-optimality in $O((1+(R/r)^{2/3})\log(2\Delta/\varepsilon))$ ball queries
-- statement:
--   **Theorem 2 (Monteiro–Svaiter acceleration).** There is an absolute constant $C > 0$ with the following property. Let $f : \mathbb R^n \to \mathbb R$ be convex and differentiable with minimizer $x^*$, let $\|x_0 - x^*\| \le R$ and $f(x_0) - f(x^*) \le \Delta$ with $R > 0$, and suppose we have a radius-$r$ ball oracle ($r > 0$) for every regularized objective $f(x) + \frac\mu2\|x - a\|^2$. For every $\varepsilon \in (0, \Delta)$:
--   1. **(implicit Euler)** the rescaled implicit Euler method of §4.2, restarted as in §5.4, has a run, and every run halts within
--   $$
--   Q \le C\,\big(1 + (R/r)^{2/3}\big)\log\frac{2\Delta}{\varepsilon}
--   $$
--   steps with an output $x$ satisfying $f(x) - f(x^*) \le \varepsilon$; each step is one ball query at a duration solving (17) exactly, or a query that returns the phase's minimizer;
--   2. **(lookahead)** the lookahead method (44), restarted in the same way, halts within $C(1 + (R/r)^{2/3})\log(2\Delta/\varepsilon)$ ball queries with an output $x$ satisfying $f(x) - f(x^*) \le \varepsilon$.
--
--   Both methods run $K = \lceil\log_2(\Delta/\varepsilon)\rceil$ restart phases; phase $k$ minimizes $f + \frac{\mu_k}{2}\|\cdot - a_k\|^2$ with $\mu_k = (\Delta/2^k)/R^2$ from the anchor $a_k$ with zero velocity, and ends when a ball query returns that objective's minimizer, which becomes $a_{k+1}$. The output is $a_K$. Neither method is given $x^*$ or $f(x^*)$.
--
--   The rate $(R/r)^{2/3}$ per halving of the gap is the Monteiro–Svaiter rate, optimal for ball-oracle methods; the theorem obtains it from a discretization of the heavy-ball ODE with a single Lyapunov function.
--
--   **Formalization Note** In clause 1 the paper writes $\tilde O$, which "hides the logarithmic cost of searching for each step duration"; the formal count is the number of steps, each one query at an exact solution of (17), as in the paper's analysis ("we treated this search as exact and let N count the number of such calls", p.14). The method's runs are a relation, so every admissible duration may be chosen.
--
--   Differences from the source:
--   - reading: Õ((1 + (R/r)^{2/3}) log 2Δ/ε) ball-oracle queries, "where Õ hides the logarithmic cost of searching for each step duration" → every run halts within C(1 + (R/r)^{2/3}) log(2Δ/ε) steps, each step one ball query at a duration solving (17) exactly or a query returning the phase minimizer; and a run exists; reason: the theorem's own Õ convention and p.14 ("we treated this search as exact and let N count the number of such calls"); bounding bisection trials is not possible with f only differentiable
--   - reading: restarted as in Section 5.4, with μ = f(a)/R² under the normalization f(x*) = 0 → phase k uses μ_k = (Δ/2^k)/R², and the method runs K = ⌈log₂(Δ/ε)⌉ phases; reason: (f(a) − f(x*))/R² cannot be computed without f(x*), which the theorem does not supply; every inequality of §5.4 holds with the gap bound Δ_k ≥ f(a_k) − f(x*) in place of the gap
--   - reading: O(·) and Õ(·) → one absolute constant C > 0 quantified before n, f, x*, x0, R, r, Δ, ε and the oracle; natural logarithm; reason: O(·) as an absolute constant; the base of the logarithm changes only C
--   - encoding: the ball oracle of eq. (1) for every regularized objective → every function O(μ, a, c) returning a minimizer of f + μ/2‖· − a‖² over the closed ball of radius r around c, for all μ ≥ 0, a, c; the gradient at an answer is read as part of that query; reason: the methods use ∇f̃ at the oracle's answer ((44); ϕ on p.14), and the paper counts only ball queries
--   - encoding: R and r without sign conditions → 0 < R and 0 < r; reason: μ_k divides by R² and the ball has radius r; R = 0 or r = 0 leaves the methods or the bound (R/r) undefined
--   - encoding: "finds x" with the stated number of queries → the method's phase counter reaches K within Q queries (it has halted), and its output, the last anchor, satisfies f(x) − f(x*) ≤ ε; reason: halting is decided by the method, never by a condition on f(x*)
--   - encoding: the lookahead phase "starting at a with zero velocity" in blocks, with "We stop the blocks once 𝓗_j ≤ μr²/2" → x̄ = a, w̄ = √μ a in original coordinates; after the last block the phase keeps that block's duration and ends at the first query with ∇f̃(x_c) = 0; reason: zero velocity is v = w̄ − √μ x̄ = 0; the page shows the next query returns the minimizer, so no other stopping rule is added
--   - encoding: the lookahead method (27) with the ball oracle (36) → its explicit form (44) (laUpdate) run on f̃_k with ∇f̃_k(x_c) = ∇f(x_c) + μ_k(x_c − a_k); reason: (44) is (27) with λ(x_p − x_c) = ∇f(x_c) substituted (eq. (36), p.21); the iterates are the same
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), Theorem 2, p.5 (methods: §4.2, pp.12–14; (44), p.23; §5.4, pp.24–25)

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_phaseMu
import Definitions.Def_UnivAccel_IsIERun
import Definitions.Def_UnivAccel_lookRun

namespace UnivAccel

/-- Theorem 2 (Monteiro–Svaiter acceleration), p.5 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)). Let `f` be convex and
differentiable with minimizer `x*`, let `‖x0 − x*‖ ≤ R` and `f(x0) − f(x*) ≤ Δ`, and suppose we have
a radius-`r` ball oracle for every regularized objective `f(x) + μ/2 ‖x − a‖²`. For every
`ε ∈ (0, Δ)`, the rescaled implicit Euler method (Section 4.2), restarted as in Section 5.4, finds
`x` with `f(x) − f(x*) ≤ ε` using `Õ((1 + (R/r)^{2/3}) log 2Δ/ε)` ball-oracle queries, where `Õ` hides
the logarithmic cost of searching for each step duration. The lookahead method (27), restarted in
the same way, does so using `O((1 + (R/r)^{2/3}) log 2Δ/ε)` ball-oracle queries.

**Formalization Note** One absolute constant `C > 0` is quantified before the dimension and all
data. Clause (a): a run of the implicit-Euler method (`IsIERun`, any admissible step durations)
exists, and every run has halted within `C(1 + (R/r)^{2/3}) log(2Δ/ε)` steps, each step one ball
query at a duration solving (17) (or ending a phase): this is the theorem's `Õ`, which hides the
search for each duration. Clause (b): the deterministic restarted lookahead method (`lookRun`,
indexed by the number of ball queries) has halted within the same bound. Both methods run
`⌈log₂(Δ/ε)⌉` phases with `μ_k = (Δ/2^k)/R²` and output the last anchor; neither receives `x*` or
`f(x*)`. `R > 0`, `r > 0` are needed for the methods to be defined. -/
theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (xstar x0 : EuclideanSpace ℝ (Fin n))
      (R r Δ ε : ℝ)
      (O : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      ConvexOn ℝ Set.univ f → Differentiable ℝ f → (∀ y, f xstar ≤ f y) →
      0 < R → 0 < r → ‖x0 - xstar‖ ≤ R → f x0 - f xstar ≤ Δ →
      0 < ε → ε < Δ → IsBallOracle f r O →
      ((∃ s : ℕ → IEState (EuclideanSpace ℝ (Fin n)), IsIERun f O R r Δ ε x0 s) ∧
        ∀ s : ℕ → IEState (EuclideanSpace ℝ (Fin n)), IsIERun f O R r Δ ε x0 s →
          ∃ Q : ℕ, (Q : ℝ) ≤ C * (1 + (R / r) ^ ((2 : ℝ) / 3)) * Real.log (2 * Δ / ε) ∧
            numPhases Δ ε ≤ (s Q).phase ∧ f (s Q).anchor - f xstar ≤ ε) ∧
      (∃ Q : ℕ, (Q : ℝ) ≤ C * (1 + (R / r) ^ ((2 : ℝ) / 3)) * Real.log (2 * Δ / ε) ∧
        numPhases Δ ε ≤ (lookRun f O R r Δ ε x0 Q).phase ∧
        f (lookRun f O R r Δ ε x0 Q).anchor - f xstar ≤ ε) := by sorry

end UnivAccel
