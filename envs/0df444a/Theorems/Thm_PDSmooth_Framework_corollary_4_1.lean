-- Prove2me | Theorems.Thm_PDSmooth_Framework_corollary_4_1
-- name    : PDSmooth.Framework.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:44.103495+00:00
-- url     : https://prove2.me/theorems/d5dfa548-6a0b-4dc9-98b0-7841287800f9
-- title:
--   Corollary 4.1, p. 17 — Algorithm 1 returns an ε-NS point of (1.1) within ⌈32β²(q(x₁) − q*)/(5ε²λ(γλ − 0.8))⌉ + 1 iterations
-- statement:
--   Let $\mathbb X,\mathbb Y$ be finite-dimensional real normed spaces and suppose the standing assumptions of problem (1.1) hold, with weak-convexity modulus $\gamma>0$ and gradient-Lipschitz constant $\beta_{\mathcal X}\ge1$ of the distance generating function $\omega_{\mathcal X}$. Let $\lambda\in(0.8\gamma^{-1},\gamma^{-1})$, $\varepsilon>0$, let $\eta=\varepsilon^2\lambda(1-\gamma\lambda)/(32\beta_{\mathcal X}^2)$ as in (4.18), and let $q^*$ be a lower bound of $q$ on $\mathcal X$ (for instance the optimal value of (1.1)). Then every run $(x_k)_{k\ge1}$ of Algorithm 1 terminates at a first iteration $K\ge1$ at which the stopping test (4.6) holds, with
--
--   $$
--   K\le\bar K:=\left\lceil\frac{32\,\beta_{\mathcal X}^2\,(q(x_1)-q^*)}{5\,\varepsilon^2\lambda(\gamma\lambda-0.8)}\right\rceil+1, \tag{4.31}
--   $$
--
--   and its output $x_K$ is an $\varepsilon$-NS point of (1.1): for some $0<\lambda'<\gamma^{-1}$ a Bregman proximal point $p=\mathrm{prox}(q,x_K,\lambda')$ exists and $\|\lambda'^{-1}(x_K-p)\|\le\varepsilon/\beta_{\mathcal X}$.
--
--   This is the outer-loop guarantee of the primal-dual smoothing framework: an explicit number of approximate proximal steps on the dually smoothed objective suffices to reach an $\varepsilon$-near-stationary point of the non-smooth, non-convex max-structured problem, in an arbitrary (non-Hilbertian) norm.
--
--   **Formalization Note** "Returns ... in no more than $\bar K$ iterations" is encoded as the existence of the first stopping index $K\le\bar K$ together with the $\varepsilon$-NS property of $x_K$. The optimal value is encoded as any lower bound of $q$ on $\mathcal X$ (equivalent, since a smaller $q^*$ only enlarges $\bar K$). The existence of the proximal point and the termination of the run are part of the conclusion, not hypotheses. Finite dimensionality is the paper's standing setting.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 17, Corollary 4.1, (4.31)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

namespace PDSmooth.Framework

/-- Corollary 4.1, p. 17: for `λ ∈ (0.8γ⁻¹, γ⁻¹)`, `ε > 0` and `η` as in (4.18), every run of
Algorithm 1 terminates at a first iteration `K ≥ 1` with
`K ≤ ⌈32 β_X² (q(x₁) − q*)/(5 ε² λ (γλ − 0.8))⌉ + 1` (4.31), and its output `x_K` is an `ε`-NS point of
(1.1); `q*` is any lower bound of `q` on `X` (in particular the optimal value of (1.1)). -/
theorem corollary_4_1 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam ε η qstar : ℝ) (hlam0 : 0.8 * γ⁻¹ < lam) (hlam1 : lam < γ⁻¹) (hε : 0 < ε)
    (hη : η = ε ^ 2 * lam * (1 - γ * lam) / (32 * βX ^ 2))
    (hqstar : ∀ z ∈ X, qstar ≤ qObj Φ g r Y z)
    (x : ℕ → E) (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x) :
    ∃ K : ℕ, 1 ≤ K ∧
      (K : ℤ) ≤ ⌈32 * βX ^ 2 * (qObj Φ g r Y (x 1) - qstar) / (5 * ε ^ 2 * lam * (γ * lam - 0.8))⌉ + 1 ∧
      Stops γ lam η x K ∧ (∀ j : ℕ, 1 ≤ j → j < K → ¬ Stops γ lam η x j) ∧
      IsNSPoint (qObj Φ g r Y) ωX X γ βX ε (x K) := by sorry
end PDSmooth.Framework
