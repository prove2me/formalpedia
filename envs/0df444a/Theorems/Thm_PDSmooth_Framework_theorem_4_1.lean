-- Prove2me | Theorems.Thm_PDSmooth_Framework_theorem_4_1
-- name    : PDSmooth.Framework.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:38.640102+00:00
-- url     : https://prove2.me/theorems/a22d1d8b-5cbf-4008-ac88-d26613725861
-- title:
--   Theorem 4.1, p. 16 — with η = ε²λ(1 − γλ)/(32β_X²), ‖x_K − prox(q,x_K,λ)‖ ≤ ελ/β_X and x_K is an ε-NS point (first stopping index K)
-- statement:
--   Under the standing assumptions of problem (1.1), with $\mathbb X$ and $\mathbb Y$ finite-dimensional, let $\varepsilon>0$ and $0<\lambda<\gamma^{-1}$, and set the accuracy parameter
--
--   $$
--   \eta=\frac{\varepsilon^2\lambda(1-\gamma\lambda)}{32\,\beta_{\mathcal X}^2}. \tag{4.18}
--   $$
--
--   Let $(x_k)_{k\ge1}$ be a run of Algorithm 1 and $K\ge1$ the first iteration at which the stopping test (4.6) holds. Then
--
--   1. every Bregman proximal point $p=\mathrm{prox}(q,x_K,\lambda)$ satisfies $\|x_K-p\|\le\varepsilon\lambda/\beta_{\mathcal X}$, and
--   2. $x_K$ is an $\varepsilon$-NS point of (1.1); in particular $\mathrm{prox}(q,x_K,\lambda)$ exists.
--
--   This is the accuracy guarantee of the framework: its output is an $\varepsilon$-near-stationary point of the non-smooth, non-convex problem (1.1) in the sense (2.10), measured in an arbitrary norm.
--
--   **Formalization Note** The paper's proof presupposes that Algorithm 1 terminates; the theorem is stated at a first stopping index $K$ and makes no termination claim (termination is Theorem 4.2). Item 2 asserts the existence of the proximal point; it is not assumed.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 16, Theorem 4.1, (4.18)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

namespace PDSmooth.Framework

/-- Theorem 4.1, p. 16: with `η = ε²λ(1 − γλ)/(32 β_X²)` (4.18), at the first iteration `K ≥ 1`
at which (4.6) holds, `‖x_K − prox(q, x_K, λ)‖ ≤ ελ/β_X`, and `x_K` is an `ε`-NS point of (1.1). -/
theorem theorem_4_1 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam ε η : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (hε : 0 < ε)
    (hη : η = ε ^ 2 * lam * (1 - γ * lam) / (32 * βX ^ 2))
    (x : ℕ → E) (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x)
    (K : ℕ) (hK1 : 1 ≤ K) (hKstop : Stops γ lam η x K)
    (hKfirst : ∀ j : ℕ, 1 ≤ j → j < K → ¬ Stops γ lam η x j) :
    (∀ p : E, IsProx (qObj Φ g r Y) ωX X lam (x K) p → ‖x K - p‖ ≤ ε * lam / βX) ∧
      IsNSPoint (qObj Φ g r Y) ωX X γ βX ε (x K) := by sorry
end PDSmooth.Framework
