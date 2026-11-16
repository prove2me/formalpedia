-- Prove2me | Theorems.Thm_SmoothedNash_Supplement_theorem_4_5
-- name    : SmoothedNash.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:10:28.717646+00:00
-- url     : https://prove2.me/theorems/4b2f05b4-84fa-4657-aafc-780f84e3ab03
-- title:
--   Theorem 4.5 — along a branch of length $T$ with $\sigma_n(J_K) \ge \theta$, Algorithm 4 finds an $\varepsilon$-VI solution in $O(1 + T\max\{L_J/\theta, a/\varepsilon\})$ oracle calls
-- statement:
--   Let $F : B(0,1) \to \mathbb R^n$ satisfy Assumptions 1.8, 1.9 and 1.10 with constants $L_0, L_1, L_2$, write $a = L_0 + L_1$ (assumed $\ge 1$, the standing convention of §4.1.1) and $L_J = 2L_2/a + 2(1 + L_1/a)$, and let $K(x,t) = (1-t)x - tF(x)/a$. Let $\varepsilon > 0$ and $0 < \theta \le 1$, and suppose the branch of zeros of $K$ leaving $(0,0)$ into $t > 0$, stopped at its first point with $t = 1$ or $\|x\| = 1$, has finite length $T$ and satisfies $\sigma_n(J_K) \ge \theta$ along it.
--
--   **Theorem.** There is a universal constant $C$ such that Algorithm 4 with the stopping predicate of Lemma 4.4 satisfies:
--
--   1. a terminated run exists (every step can be carried out until the predicate stops the loop);
--   2. every run uses at most
--   $$
--   C\Bigl(1 + T \max\Bigl\{\frac{L_J}{\theta}, \frac{a}{\varepsilon}\Bigr\}\Bigr)
--   $$
--   zeroth- and first-order oracle calls, and its running time, with a constant number of calls and $(n+1)^\kappa$ arithmetic per iteration, is at most $C (n+1)^\kappa$ times the same quantity;
--   3. all queried points lie in the unit ball;
--   4. every terminated run returns an $\varepsilon$-approximate variational inequality solution.
--
--   This is the deterministic analysis of the predictor–corrector homotopy method: it reduces the running time to the length of the path and its conditioning, which Theorem 4.17 then bounds in the smoothed model.
--
--   **Formalization Note** $\mathbb R^{n+1}$ is $\mathbb R^n \times \mathbb R$ with the Euclidean norm written out. The run is a relation (any admissible choice in lines 9 and 11), so clauses 2–4 hold for every choice. Oracle calls are counted with two calls per evaluation of the predicate. Clause 3 concerns runs that pass line 1; otherwise the only query is $F(0)$.
--
--   Differences from the source:
--
--   - reading: a = L0 + L1; without loss of generality a ≥ 1 (§4.1.1, p.26) → hypothesis 1 ≤ L0 + L1; reason: the standing assumption of Section 4, stated once at its top
--   - reading: Algorithm 4 finds an ε-approximate VI solution using O(1 + T max{L_J/θ, a/ε}) calls → ∃ universal C > 0: a terminated run exists, every run has alg4Calls ≤ C(1 + T max{L_J/θ, a/ε}), and every terminated run outputs an ε-approximate VI solution; reason: the algorithm's choices in lines 9 and 11 are relations, so existence and a bound over all runs is the full claim; O(·) is a universal constant
--   - reading: each iteration uses a constant number of calls and polynomially many arithmetic operations in n → ∀ κ, alg4Runtime κ ≤ C (n+1)^κ (1 + T max{L_J/θ, a/ε}) with alg4Runtime = (calls + N + 1)(n+1)^κ; reason: the polynomial is unspecified; every exponent is covered
--   - encoding: zeroth- and first-order oracle calls → alg4Calls = 1 at an immediate return, else 6N + 3; reason: two calls charged per evaluation of H (Lemma 4.4) and one per F or J_F value at x̄_i, ȳ_i; constant factors are absorbed in C
--   - encoding: the followed lifted branch with finite length T and σ_n(J_K) ≥ θ along it → IsFollowedBranch: unit-speed C¹ zero curve of K from (0,0) in direction (F(0)/a, 1), stopped at its first point with ‖x‖ = 1 or t = 1, with θ ≤ σ_n on [0, T]; reason: the paper's description of the branch, spelled out
--   - encoding: Jacobian J_F on B(0,1) → fderivWithin on the closed ball, with DifferentiableOn; reason: depends only on F on the ball; unique on a convex body
--   - encoding: n-dimensional problem → 1 ≤ n; reason: σ_n of an n × (n+1) matrix is undefined for n = 0
--   - encoding: all queried points lie in the unit ball → for runs past line 1: x̄_i ∈ B for i ≤ N and ȳ_i ∈ B for i < N; reason: at an immediate return the only query is F(0); the point x̄/‖x̄‖ queried by H is on the sphere
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Theorem 4.5, pp.28–29 (Algorithm 4 and Lemma 4.4, pp.27–28; §4.1, p.26)

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_IsApproxVI
import Definitions.Def_SmoothedNash_Supplement_BoundedNorm
import Definitions.Def_SmoothedNash_Supplement_LipschitzOnBall
import Definitions.Def_SmoothedNash_Supplement_JacobianLipschitz
import Definitions.Def_SmoothedNash_Supplement_lipJK
import Definitions.Def_SmoothedNash_Supplement_IsFollowedBranch
import Definitions.Def_SmoothedNash_Supplement_stepSize
import Definitions.Def_SmoothedNash_Supplement_IsAlg4Trace
import Definitions.Def_SmoothedNash_Supplement_IsAlg4Terminated
import Definitions.Def_SmoothedNash_Supplement_alg4Out
import Definitions.Def_SmoothedNash_Supplement_alg4Calls
import Definitions.Def_SmoothedNash_Supplement_alg4Runtime
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Theorem 4.5** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), pp.28–29). Under Assumptions 1.8, 1.9, 1.10, and 1.11, suppose
the followed lifted branch has finite length `T` and `σ_n(J_K) ≥ θ` along this branch, where
`0 < θ ≤ 1`. With the stopping predicate of Lemma 4.4, Algorithm 4 finds an `ε`-approximate
variational inequality solution using `O(1 + T max{L_J/θ, a/ε})` zeroth-order and first-order oracle
calls. Each iteration uses a constant number of these calls and polynomially many arithmetic
operations in `n` for a kernel computation and a linear-system solve. The statement uses exact real
arithmetic; all queried points lie in the unit ball.

With `a = L0 + L1`, `L_J = lipJK L0 L1 L2` and `h = stepSize`, there is one universal `C > 0` such
that, for every `n ≥ 1`, every `F` satisfying Assumptions 1.8–1.10, every `ε > 0`, `0 < θ ≤ 1`, and
every branch `γ` of length `T` as in `IsFollowedBranch`:
1. a terminated run of Algorithm 4 exists;
2. every run (terminated or not) of `N` iterations uses at most `C (1 + T max{L_J/θ, a/ε})` oracle
   calls, and its running time is at most `C (n + 1)^κ (1 + T max{L_J/θ, a/ε})` for every `κ`; in
   particular every run terminates within this bound;
3. every queried point lies in the unit ball: `x̄_i` for `i ≤ N` and `ȳ_i = x̄_i + h v̄_i` for `i < N`;
4. the output of every terminated run is an `ε`-approximate variational inequality solution for `F`.

**Formalization Note** Assumption 1.11 (oracle access) is the oracle model, counted by `alg4Calls`.
`a ≥ 1` is the standing "without loss of generality" of §4.1.1 (p.26), taken as a hypothesis. The
`O(·)` is the universal constant `C`, independent of `n, F, ε, θ, L0, L1, L2, T`. Clause 3 is stated for
runs past line 1; if `‖F(0)‖ ≤ ε/2` the only query is `F(0)`. `n ≥ 1` because `σ_n` is undefined for
`n = 0`. -/
theorem theorem_4_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ}, 1 ≤ n →
      ∀ (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (L0 L1 L2 ε θ T : ℝ)
        (γx : ℝ → EuclideanSpace ℝ (Fin n)) (γt : ℝ → ℝ),
        1 ≤ L0 + L1 → 0 < ε → 0 < θ → θ ≤ 1 →
        BoundedNorm F L0 → LipschitzOnBall F L1 → JacobianLipschitz F L2 →
        IsFollowedBranch F L0 L1 θ T γx γt →
        (∃ p v N, IsAlg4Terminated F L0 L1 L2 ε θ p v N) ∧
        (∀ p v N, IsAlg4Trace F L0 L1 L2 ε θ p v N →
          (alg4Calls F ε N : ℝ) ≤ C * (1 + T * max (lipJK L0 L1 L2 / θ) ((L0 + L1) / ε)) ∧
          ∀ κ : ℕ, alg4Runtime κ F ε N ≤
            C * ((n : ℝ) + 1) ^ κ * (1 + T * max (lipJK L0 L1 L2 / θ) ((L0 + L1) / ε))) ∧
        (∀ p v N, IsAlg4Trace F L0 L1 L2 ε θ p v N → ε / 2 < ‖F 0‖ →
          (∀ i ≤ N, (p i).1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
          ∀ i < N, (p i + stepSize L0 L1 L2 ε θ • v (i + 1)).1 ∈
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
        (∀ p v N, IsAlg4Terminated F L0 L1 L2 ε θ p v N →
          IsApproxVI F ε (alg4Out F L0 L1 ε p N)) := by sorry

end SmoothedNash.Supplement
