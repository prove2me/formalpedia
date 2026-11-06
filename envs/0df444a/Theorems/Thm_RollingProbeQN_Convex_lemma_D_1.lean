-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_D_1
-- name    : RollingProbeQN.Convex.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:30.257662+00:00
-- url     : https://prove2.me/theorems/9b8ea072-9202-425e-ac3b-38f2dbe9f743
-- title:
--   Lemma D.1 — potential decrease of the A-HPE recursion and its consequences
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be convex and differentiable with a minimizer $x^\star$, $F^\star=F(x^\star)$, let $\sigma\in(0,1)$, and let $(\lambda_k,x_k,y_k,z_k,A_k)$ be an A-HPE run for $F$ and $\sigma$ up to horizon $N$ with $\|x_0-x^\star\|\le R$. Write $r_k=x_{k+1}-y_k$ and
--
--   $$\Psi_k=A_k\big(F(x_k)-F^\star\big)+\tfrac12\|z_k-x^\star\|^2 .$$
--
--   Then for every $k<N$
--
--   $$\Psi_{k+1}\le\Psi_k-\frac{1-\sigma^2}{2}\cdot\frac{A_{k+1}}{\lambda_k}\|r_k\|^2,$$
--
--   and, if $N\ge1$:
--
--   1. $F(x_N)-F^\star\le R^2/(2A_N)$;
--   2. $\|z_k-x^\star\|\le R$ for every $k\le N$;
--   3. $\displaystyle\sum_{k=0}^{N-1}\frac{A_{k+1}}{\lambda_k}\|r_k\|^2\le\frac{R^2}{1-\sigma^2}$.
--
--   This is the Monteiro–Svaiter potential argument; it gives the objective bound used for both branches of Theorem 3.1 and the movement energy used to control path lengths.
--
--   Differences from the source:
--   - encoding: the recursion runs for k = 0, 1, … and the claim is for every k ≥ 0 → an A-HPE run up to an arbitrary horizon N, the claim for k < N (resp. k ≤ N); reason: N is arbitrary, so every finite stretch of an infinite run is covered; same instances
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma D.1, p. 37

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_IsAHPERun

namespace RollingProbeQN.Convex

/-- **Lemma D.1 (Potential decrease).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma D.1, p. 37.

Let `F` be convex and differentiable with a minimizer `x★`, `σ ∈ (0, 1)`, `‖x_0 − x★‖ ≤ R`, and let
`(λ_k, x_k, y_k, z_k, A_k)` be an A-HPE run up to horizon `N`. With
`Ψ_k = A_k(F(x_k) − F★) + ½‖z_k − x★‖²` and `r_k = x_{k+1} − y_k`: for every `k < N`,
`Ψ_{k+1} ≤ Ψ_k − (1 − σ²)/2 · A_{k+1}/λ_k · ‖r_k‖²`; and if `N ≥ 1`, then
(i) `F(x_N) − F★ ≤ R²/(2A_N)`, (ii) `‖z_k − x★‖ ≤ R` for `k ≤ N`,
(iii) `∑_{k<N} A_{k+1}/λ_k ‖r_k‖² ≤ R²/(1 − σ²)`.

**Formalization Note.** The standing assumptions of Appendix D.1 (`F` convex differentiable with a
minimizer, `‖x_0 − x★‖ ≤ R`, `A_0 = 0`, `x_0 = z_0`, positive stepsizes, condition (2)) are the
hypotheses; the run is finite (horizon `N`), so "for every `k ≥ 0`" is "for every `k < N`", for
every `N`. -/
theorem lemma_D_1 {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → ℝ} {σ R : ℝ} {N : ℕ} {lam : ℕ → ℝ}
    {x y z : ℕ → EuclideanSpace ℝ (Fin d)} {A : ℕ → ℝ} {xstar : EuclideanSpace ℝ (Fin d)}
    (hconv : ConvexOn ℝ Set.univ F) (hdiff : Differentiable ℝ F)
    (hmin : IsMinOn F Set.univ xstar) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hR : ‖x 0 - xstar‖ ≤ R)
    (hrun : IsAHPERun F σ N lam x y z A) :
    (∀ k < N,
      A (k + 1) * (F (x (k + 1)) - F xstar) + 1 / 2 * ‖z (k + 1) - xstar‖ ^ 2 ≤
        A k * (F (x k) - F xstar) + 1 / 2 * ‖z k - xstar‖ ^ 2
          - (1 - σ ^ 2) / 2 * (A (k + 1) / lam k) * ‖x (k + 1) - y k‖ ^ 2) ∧
    (1 ≤ N →
      F (x N) - F xstar ≤ R ^ 2 / (2 * A N) ∧
      (∀ k ≤ N, ‖z k - xstar‖ ≤ R) ∧
      ∑ k ∈ Finset.range N, A (k + 1) / lam k * ‖x (k + 1) - y k‖ ^ 2 ≤ R ^ 2 / (1 - σ ^ 2)) := by sorry

end RollingProbeQN.Convex
