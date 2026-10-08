-- Prove2me | Theorems.Thm_SDCA_Smooth_eq_12
-- name    : SDCA.Smooth.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:41.306746+00:00
-- url     : https://prove2.me/theorems/7444d25c-adf1-4574-94ea-82deb7d16277
-- title:
--   Eq. (12): the expected duality gap is at most $(n/s)$ times the expected dual sub-optimality
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $n\ge1$ and $\|x_i\|\le1$, let $\lambda,\gamma>0$, and let the losses $\varphi_i$ be convex, $(1/\gamma)$-smooth and nonnegative. Run Procedure SDCA from $\alpha^{(0)}=0$ with an SDCA step and coordinates chosen independently and uniformly, write $w^{(t)}=w(\alpha^{(t)})$, let $\alpha^*$ maximize $D$, and put $\epsilon_D^{(t)}=D(\alpha^*)-D(\alpha^{(t)})$ and $s=\frac{\lambda n\gamma}{1+\lambda n\gamma}$. Then $D(\alpha^*)$ and all $D(\alpha^{(t)})$ are finite, and for every $t\ge0$
--   $$\mathbb E\big[P(w^{(t)})-D(\alpha^{(t)})\big]\ \le\ \frac ns\,\mathbb E\big[\epsilon_D^{(t)}-\epsilon_D^{(t+1)}\big]\ \le\ \frac ns\,\mathbb E\big[\epsilon_D^{(t)}\big].$$
--
--   The duality gap at a given iterate is controlled by the dual sub-optimality; summed over $t=T_0,\dots,T-1$ it also controls the gap of the averaged output.
--
--   **Formalization Note** All three expectations are uniform averages over the first $t+1$ coordinate choices (`SAGA.Convex.expectIdx n (t+1)`); quantities at iterate $t$ depend only on the first $t$. Dual values are `EReal`, converted to reals under the finiteness conjuncts. The standing assumption $\varphi_i(0)\le1$ is not needed and not assumed.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, proof of Theorem 2, p. 14, eq. (12)

import Mathlib
import Definitions.Def_SDCA_Smooth_Model

namespace SDCA.Smooth

/-- Eq. (12), §7.1, p. 14 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2). Run Procedure SDCA from
`α⁽⁰⁾ = 0` with `(1/γ)`-smooth convex losses, `‖xᵢ‖ ≤ 1` and `φᵢ ≥ 0`, let `α*` maximize `D`, put
`ε_D⁽ᵗ⁾ = D(α*) − D(α⁽ᵗ⁾)` and `s = λnγ/(1 + λnγ)`. Then all these dual values are finite, and for
every `t`, with expectations over the first `t + 1` i.i.d. uniform coordinates,
`E[P(w⁽ᵗ⁾) − D(α⁽ᵗ⁾)] ≤ (n/s) E[ε_D⁽ᵗ⁾ − ε_D⁽ᵗ⁺¹⁾] ≤ (n/s) E[ε_D⁽ᵗ⁾]`, where `w⁽ᵗ⁾ = w(α⁽ᵗ⁾)`. -/
theorem eq_12 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ φ' : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ)
    (hderiv : ∀ i a, HasDerivAt (φ i) (φ' i a) a)
    (hsmooth : ∀ i a b, |φ' i a - φ' i b| ≤ (1 / γ) * |a - b|)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hφnn : ∀ i a, 0 ≤ φ i a)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (αstar : Fin n → ℝ) (hαstar : ∀ β, dual lam x φ β ≤ dual lam x φ αstar) :
    dual lam x φ αstar ≠ ⊥ ∧
    (∀ (T : ℕ) (js : Fin T → Fin n) (t : ℕ), dual lam x φ (alphaIter Δ js t) ≠ ⊥) ∧
    ∀ t : ℕ,
      SAGA.Convex.expectIdx n (t + 1) (fun js =>
          primal lam x φ (wOf lam x (alphaIter Δ js t)) -
            (dual lam x φ (alphaIter Δ js t)).toReal) ≤
        n / (lam * n * γ / (1 + lam * n * γ)) *
          SAGA.Convex.expectIdx n (t + 1) (fun js =>
            ((dual lam x φ αstar).toReal - (dual lam x φ (alphaIter Δ js t)).toReal) -
              ((dual lam x φ αstar).toReal - (dual lam x φ (alphaIter Δ js (t + 1))).toReal)) ∧
      n / (lam * n * γ / (1 + lam * n * γ)) *
          SAGA.Convex.expectIdx n (t + 1) (fun js =>
            ((dual lam x φ αstar).toReal - (dual lam x φ (alphaIter Δ js t)).toReal) -
              ((dual lam x φ αstar).toReal - (dual lam x φ (alphaIter Δ js (t + 1))).toReal)) ≤
        n / (lam * n * γ / (1 + lam * n * γ)) *
          SAGA.Convex.expectIdx n (t + 1) (fun js =>
            (dual lam x φ αstar).toReal - (dual lam x φ (alphaIter Δ js t)).toReal) := by sorry

end SDCA.Smooth
