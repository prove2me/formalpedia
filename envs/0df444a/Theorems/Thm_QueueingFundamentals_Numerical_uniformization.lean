-- Prove2me | Theorems.Thm_QueueingFundamentals_Numerical_uniformization
-- name    : QueueingFundamentals.Numerical.uniformization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T20:25:11.746163+00:00
-- url     : https://prove2.me/theorems/cf41ad24-e6cb-4d1f-85c4-5353d383c9a8
-- title:
--   Eqs. (8.9)–(8.12) — the randomization (uniformization) formula with truncation bound
-- statement:
--   Let $X(t)$ be a continuous-time Markov chain on $\{0,1,\dots,N\}$ with infinitesimal generator $Q=(q_{ij})$, where $q_{ij}\ge 0$ for $i\ne j$ and the diagonal entries are $-q_i$ with $q_i=\sum_{j\ne i}q_{ij}$. Let $\Lambda>0$ satisfy $\Lambda\ge q_i$ for every $i$, let $\tilde P=Q/\Lambda+I$, and let $p(0)$ be an initial probability vector. The transient state-probability vector $p(t)=(p_0(t),\dots,p_N(t))$ is the solution of the forward equations
--
--   $$p'(t)=p(t)Q\quad(t\ge0),\qquad p(0)\text{ given}.$$
--
--   Then this system has a solution, and every solution satisfies, for all $t\ge 0$:
--
--   1. (8.9) the randomization formula
--   $$p(t)=\sum_{k=0}^{\infty}p(0)\tilde P^{(k)}\,\frac{e^{-\Lambda t}(\Lambda t)^k}{k!},$$
--   with the series converging in every component;
--   2. (8.10)–(8.11) the truncation bound: if $T$ is such that
--   $$\sum_{k=0}^{T}\frac{e^{-\Lambda t}(\Lambda t)^k}{k!}>1-\epsilon,$$
--   then for every state $n$ the $n$-th component of the truncated sum $\sum_{k=0}^{T}p(0)\tilde P^{(k)}e^{-\Lambda t}(\Lambda t)^k/k!$ differs from $p_n(t)$ by less than $\epsilon$.
--
--   The formula reduces the transient analysis of a continuous-time chain to powers of a stochastic matrix weighted by Poisson probabilities, with an a-priori choice of the truncation point.
--
--   **Formalization Note** The book derives the formula for a birth–death generator and then asserts it for any finite generator (p.384); the general finite form is stated. The book takes $\Lambda=\max_i q_i$; any $\Lambda\ge\max_i q_i$ is allowed. The book's display (8.9) prints $e^{-\lambda t}$ where $e^{-\Lambda t}$ is meant. The existence of a solution is stated explicitly, so the statement is not vacuous; uniqueness is implicit in "every solution".
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.383–384, Eqs. (8.9)–(8.12)

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_Uniformization

open Matrix

namespace QueueingFundamentals.Numerical

/-- Eqs. (8.9)–(8.12), the randomization (uniformization) formula (Gross et al., pp.383–384).
Let `Q` be the generator of a continuous-time Markov chain on `{0, …, N}`, `Λ > 0` with
`Λ ≥ q_i` for every state, `P̃ = Q/Λ + I`, and `p(0)` an initial probability vector. Then
the forward equations `p′(t) = p(t)Q` have a solution with `p(0) = p₀`, and every such solution
satisfies, for every `t ≥ 0`:
(8.9) `p(t) = ∑_{k ≥ 0} p(0) P̃^{(k)} e^{−Λt}(Λt)^k/k!` componentwise, and
(8.10)–(8.11) whenever `∑_{k=0}^{T} e^{−Λt}(Λt)^k/k! > 1 − ε`, each component of the truncated
sum `∑_{k=0}^{T} p(0) P̃^{(k)} e^{−Λt}(Λt)^k/k!` is within `ε` of `p_n(t)`. -/
theorem uniformization {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (Λ : ℝ) (hΛ : 0 < Λ) (hΛq : ∀ i, exitRate Q i ≤ Λ)
    (p₀ : Fin (N + 1) → ℝ) (hp₀ : IsProbVec p₀) :
    (∃ p : ℝ → Fin (N + 1) → ℝ, SolvesForward Q p₀ p) ∧
      ∀ p : ℝ → Fin (N + 1) → ℝ, SolvesForward Q p₀ p → ∀ t : ℝ, 0 ≤ t →
        (∀ n, HasSum (fun k : ℕ => poissonWeight Λ t k * phi Λ Q p₀ k n) (p t n)) ∧
        ∀ (T : ℕ) (ε : ℝ), 1 - ε < ∑ k ∈ Finset.range (T + 1), poissonWeight Λ t k →
          ∀ n, |p t n - truncatedSolution Λ Q p₀ t T n| < ε := by sorry

end QueueingFundamentals.Numerical
