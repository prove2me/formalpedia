-- Prove2me | Theorems.Thm_SDCA_AlmostSmooth_theorem_5
-- name    : SDCA.AlmostSmooth.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:06:34.391886+00:00
-- url     : https://prove2.me/theorems/556e75c2-fd52-4ca4-bb23-1d46b6bcb371
-- title:
--   Theorem 5 — under (5), SDCA reaches $\mathbb E[D(\alpha^*)-D(\alpha^{(t)})]\le\epsilon_D$ once $t\ge 2(n/s)\log(2/\epsilon_D)$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $\|x_i\|\le1$, let $\lambda>0$, and let the losses $\varphi_i:\mathbb R\to\mathbb R$ be convex, $L$-Lipschitz, nonnegative, with $\varphi_i(0)\le1$. Run Procedure SDCA from $\alpha^{(0)}=0$, each iteration choosing its coordinate uniformly at random and independently and performing an exact coordinate maximization of the dual. Let $\alpha^*$ maximize the dual objective $D$ of (2), and suppose the dual strong convexity inequality (5) holds at $\alpha^*$ with constants $\gamma_1,\dots,\gamma_n\ge0$ and $w^*=w(\alpha^*)$:
--   $$
--   D(\alpha^*)-D(\alpha)\ge\frac1n\sum_{i=1}^n\gamma_i|\alpha_i-\alpha_i^*|^2+\frac\lambda2\|w(\alpha)-w^*\|^2\quad\text{for every feasible }\alpha .
--   $$
--   Define $N(u)=\#\{i:\gamma_i<u\}$. Then $D(\alpha^*)$ and every $D(\alpha^{(t)})$ are finite, and for every $\epsilon_D>0$ and every $s\in(0,1]$ with
--   $$
--   \epsilon_D\ge\frac{8L^2\,\frac{s}{\lambda n}\,N\bigl(\frac{s}{\lambda n}\bigr)}{n},
--   $$
--   every number of iterations
--   $$
--   t\ge2\,\frac ns\,\log\frac{2}{\epsilon_D}
--   $$
--   gives
--   $$
--   \mathbb E\bigl[D(\alpha^*)-D(\alpha^{(t)})\bigr]\le\epsilon_D .
--   $$
--
--   When few of the constants $\gamma_i$ are small, $s$ can be taken close to $1$ and the dual sub-optimality decreases at a linear rate, even for non-smooth losses such as the hinge loss.
--
--   **Formalization Note** The expectation is the uniform average over all coordinate sequences of length $t$ (`SAGA.Convex.expectIdx`); the dual values are finite (stated as part of the conclusion) and are then converted to reals. The step of Procedure SDCA is any map $\Delta$ that is an exact maximizer of the coordinate objective. The paper prints $s\in[0,1]$; $s=0$ is excluded, since there $2(n/s)\log(2/\epsilon_D)$ is undefined (Lean would read it as $0$ and the claim would fail at $t=0$). $L$-Lipschitz is $|\varphi_i(a)-\varphi_i(b)|\le L|a-b|$ as in Definition 1, with no separate sign condition on $L$.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 9, Theorem 5 (proof §7.6, pp. 19–20)

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_Model
import Definitions.Def_SAGA_Convex_sagaRun

namespace SDCA.AlmostSmooth

/-- Theorem 5 (p. 9). Procedure SDCA with `α⁽⁰⁾ = 0`, losses `φᵢ` convex and `L`-Lipschitz,
the standing assumptions `‖xᵢ‖ ≤ 1`, `φᵢ ≥ 0`, `φᵢ(0) ≤ 1`, `α*` a maximizer of `D`, and (5)
with constants `γᵢ ≥ 0`. With `N(u) = #{i : γᵢ < u}`: for every `ϵ_D > 0` and `s ∈ (0, 1]` with
`ϵ_D ≥ 8L²(s/(λn))N(s/(λn))/n`, every `t ≥ 2(n/s) log(2/ϵ_D)` gives
`E[D(α*) − D(α⁽ᵗ⁾)] ≤ ϵ_D`, the expectation over the `t` uniform coordinate choices. All dual
values involved are finite. -/
theorem theorem_5 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, ‖x i‖ ≤ 1) (φ : Fin n → ℝ → ℝ) (hφconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1) (L : ℝ)
    (hL : ∀ i, ∀ a b : ℝ, |φ i a - φ i b| ≤ L * |a - b|) (lam : ℝ) (hlam : 0 < lam)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : SDCA.Smooth.IsSDCAStep lam x φ Δ) (αstar : Fin n → ℝ)
    (hopt : ∀ β, SDCA.Smooth.dual lam x φ β ≤ SDCA.Smooth.dual lam x φ αstar) (γ : Fin n → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (h5 : DualStrongConvexity lam x φ γ αstar) :
    SDCA.Smooth.dual lam x φ αstar ≠ ⊥ ∧
      (∀ (t : ℕ) (js : Fin t → Fin n), SDCA.Smooth.dual lam x φ (SDCA.Smooth.alphaIter Δ js t) ≠ ⊥) ∧
      ∀ εD : ℝ, 0 < εD → ∀ s : ℝ, 0 < s → s ≤ 1 →
        8 * L ^ 2 * (s / (lam * n)) * (countBelow γ (s / (lam * n)) : ℝ) / n ≤ εD →
        ∀ t : ℕ, 2 * (n / s) * Real.log (2 / εD) ≤ t →
          SAGA.Convex.expectIdx n t (fun js =>
            (SDCA.Smooth.dual lam x φ αstar).toReal - (SDCA.Smooth.dual lam x φ (SDCA.Smooth.alphaIter Δ js t)).toReal) ≤ εD := by sorry

end SDCA.AlmostSmooth
