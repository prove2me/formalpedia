-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_lemma_3_4
-- name    : ProxADMMLC.Conv.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:04.882027+00:00
-- url     : https://prove2.me/theorems/28a118f4-89e2-4840-a08d-3e83bd02623d
-- title:
--   Lemma 3.4, p. 2279 — under Assumption 2.2(a), yⁱ ∈ ỹ⁰ + range(A) and ‖Ax(yⁱ, zⁱ) − b‖ → 0 imply {yⁱ} bounded
-- statement:
--   Suppose Assumption 2.2(a) holds and $f$ is differentiable; let $\Gamma,p$ be any constants and $x(y,z)$ a minimizer of $K(\cdot,z;y)$ over $P$. Let $\tilde y^0\in\mathbb R^m$ be fixed, let $\{y^i\}\subseteq\tilde y^0+\operatorname{range}(A)$, and let $\{z^i\}\subseteq P$. If
--   $$\|Ax(y^i,z^i)-b\|\to0\qquad(i\to\infty),$$
--   then the sequence $\{y^i\}$ is bounded.
--
--   By the remark after the lemma, every dual iterate $y^t$ of Algorithm 2.2 lies in $y^0+\operatorname{range}(A)$, so a vanishing dual residual forces bounded duals; this gives the boundedness claim of Theorem 2.4.
--
--   **Formalization Note** The page does not say where $z^i$ lies; its proof bounds $K$ by a maximum over $x,z\in P$, and every application has $z^i=z^t\in P$, so $z^i\in P$ is added. Differentiability of $f$ (Assumption 2.2(c)) is used only for continuity, which makes $f$ bounded on $P$.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2279, Lemma 3.4

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

open Filter Topology

namespace ProxADMMLC.Conv

theorem lemma_3_4 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (ha : Assump22a A b ℓ u) (hdiff : Differentiable ℝ f)
    (Γ p : ℝ) (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs) :
    ∀ (y0 : E m) (ys : ℕ → E m) (zs : ℕ → E n),
      (∀ i, ys i - y0 ∈ LinearMap.range (A : E n →ₗ[ℝ] E m)) → (∀ i, zs i ∈ box ℓ u) →
      Tendsto (fun i => ‖A (xs (ys i) (zs i)) - b‖) atTop (𝓝 0) →
      Bornology.IsBounded (Set.range ys) := by sorry

end ProxADMMLC.Conv
