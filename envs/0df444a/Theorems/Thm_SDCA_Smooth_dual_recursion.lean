-- Prove2me | Theorems.Thm_SDCA_Smooth_dual_recursion
-- name    : SDCA.Smooth.dual_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:45.483925+00:00
-- url     : https://prove2.me/theorems/cadfc5a3-9ecd-44ce-9330-7d7ef1224809
-- title:
--   Linear convergence of the expected dual sub-optimality: $\mathbb E[\epsilon_D^{(t)}]\le(1-s/n)^t\le\exp(-\lambda\gamma t/(1+\lambda\gamma n))$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $n\ge1$ and $\|x_i\|\le1$, let $\lambda,\gamma>0$, and let the losses $\varphi_i$ be convex and $(1/\gamma)$-smooth with $\varphi_i\ge0$ and $\varphi_i(0)\le1$. Run Procedure SDCA from $\alpha^{(0)}=0$ with an SDCA step $\Delta$ and coordinates chosen independently and uniformly, let $\alpha^*$ maximize $D$, and write
--   $$\epsilon_D^{(t)}=D(\alpha^*)-D(\alpha^{(t)}),\qquad s=\frac{\lambda n\gamma}{1+\lambda n\gamma}.$$
--   Then $D(\alpha^*)$ and all $D(\alpha^{(t)})$ are finite, and for every $t\ge0$:
--   1. $\mathbb E[\epsilon_D^{(t+1)}]\le(1-s/n)\,\mathbb E[\epsilon_D^{(t)}]$;
--   2. $\mathbb E[\epsilon_D^{(t)}]\le(1-s/n)^t\,\epsilon_D^{(0)}$;
--   3. $\epsilon_D^{(0)}\le1$;
--   4. $(1-s/n)^t\le\exp\!\big(-\frac{\lambda\gamma t}{1+\lambda\gamma n}\big)$.
--
--   Together,
--   $$\mathbb E[\epsilon_D^{(t)}]\ \le\ \Big(1-\frac sn\Big)^t\ \le\ \exp\Big(-\frac{\lambda\gamma t}{1+\lambda\gamma n}\Big),$$
--   the linear rate of the dual sub-optimality from which both parts of Theorem 2 follow.
--
--   **Formalization Note** Expectations are uniform averages over index sequences (`SAGA.Convex.expectIdx`); the one-step inequality averages both sides over the first $t+1$ indices (the right side depends only on the first $t$). Dual values are `EReal`, converted to reals under the finiteness conjuncts.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, proof of Theorem 2, p. 14, second display

import Mathlib
import Definitions.Def_SDCA_Smooth_Model

namespace SDCA.Smooth

/-- §7.1, proof of Theorem 2, p. 14, second display (Shalev-Shwartz–Zhang, arXiv:1209.1873v2):
the linear recursion for the expected dual sub-optimality. Run Procedure SDCA from `α⁽⁰⁾ = 0` with
`(1/γ)`-smooth convex losses and the standing assumptions (p. 5), let `α*` maximize `D`, put
`ε_D⁽ᵗ⁾ = D(α*) − D(α⁽ᵗ⁾)` and `s = λnγ/(1 + λnγ)`. Then all these dual values are finite, and for
every `t`:
`E[ε_D⁽ᵗ⁺¹⁾] ≤ (1 − s/n) E[ε_D⁽ᵗ⁾]`, `E[ε_D⁽ᵗ⁾] ≤ (1 − s/n)ᵗ ε_D⁽⁰⁾`, `ε_D⁽⁰⁾ ≤ 1` and
`(1 − s/n)ᵗ ≤ exp(−λγt/(1 + λγn))`. Expectations are over the i.i.d. uniform coordinates. -/
theorem dual_recursion {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ φ' : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ)
    (hderiv : ∀ i a, HasDerivAt (φ i) (φ' i a) a)
    (hsmooth : ∀ i a b, |φ' i a - φ' i b| ≤ (1 / γ) * |a - b|)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (αstar : Fin n → ℝ) (hαstar : ∀ β, dual lam x φ β ≤ dual lam x φ αstar) :
    dual lam x φ αstar ≠ ⊥ ∧
    (∀ (T : ℕ) (js : Fin T → Fin n) (t : ℕ), dual lam x φ (alphaIter Δ js t) ≠ ⊥) ∧
    ∀ t : ℕ,
      SAGA.Convex.expectIdx n (t + 1) (fun js =>
          (dual lam x φ αstar).toReal - (dual lam x φ (alphaIter Δ js (t + 1))).toReal) ≤
        (1 - lam * n * γ / (1 + lam * n * γ) / n) *
          SAGA.Convex.expectIdx n (t + 1) (fun js =>
            (dual lam x φ αstar).toReal - (dual lam x φ (alphaIter Δ js t)).toReal) ∧
      SAGA.Convex.expectIdx n t (fun js =>
          (dual lam x φ αstar).toReal - (dual lam x φ (alphaIter Δ js t)).toReal) ≤
        (1 - lam * n * γ / (1 + lam * n * γ) / n) ^ t *
          ((dual lam x φ αstar).toReal - (dual lam x φ 0).toReal) ∧
      (dual lam x φ αstar).toReal - (dual lam x φ 0).toReal ≤ 1 ∧
      (1 - lam * n * γ / (1 + lam * n * γ) / n) ^ t ≤
        Real.exp (-(lam * γ * t) / (1 + lam * γ * n)) := by sorry

end SDCA.Smooth
