-- Prove2me | Theorems.Thm_PNormReg_lemma_11
-- name    : PNormReg.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:30.821091+00:00
-- url     : https://prove2.me/theorems/9114f6ae-6e71-4631-8c4e-8c04e88402da
-- title:
--   Lemma 11, p.23 — the matrix game (21) has optimum at most 1, and the recovered $\tilde u$ is feasible for (19) with $\|\bar A\tilde u\|_p\le\xi$
-- statement:
--   With the hypotheses of Lemma 10, let $L$ satisfy $LL^\top=\bar D$ and $\rho=\tfrac12\sqrt{\|L^{-1}\bar h\|_2^2-1/2}$. The game
--
--   $$\min_{\|x\|_2\le1}\max_{\|y\|_q\le1}y^\top(\rho\bar AL^{-\top})x+\tfrac12y^\top\bar AL^{-\top}L^{-1}\bar h\tag{21}$$
--
--   has optimum at most 1. Further, if $\|\tilde x\|_2\le1$ and $\max_{\|y\|_q\le1}y^\top(\rho\bar AL^{-\top}\tilde x+\tfrac12\bar AL^{-\top}L^{-1}\bar h)\le\xi$ for some $\xi\ge1$, then
--
--   $$\tilde u:=L^{-\top}\big(\rho\tilde x+\tfrac12L^{-1}\bar h\big)$$
--
--   is feasible for (19) and satisfies $\|\bar A\tilde u\|_p\le\xi$.
--
--   This is the step from a constrained norm minimization to a bilinear game over two balls.
--
--   Differences from the source:
--   - generalization: D̄^{−1/2} (the symmetric square root) → any L with LL⊤ = D̄, with L^{−⊤} and L^{−1} in place of D̄^{−1/2}; reason: the symmetric root is one such L, so the printed statement is an instance; the Cholesky factor of p.25 is another
--   - encoding: "has optimum at most 1" → ∃ x, ∥x∥₂ ≤ 1, with h(x, y) ≤ 1 for all ∥y∥_q ≤ 1; reason: the meaning of the claim for a min–max
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Lemma 11, p.23 (PDF p.24); factorization form, p.25

import Mathlib
import Definitions.Def_PNormReg_Scaled

open Matrix

namespace PNormReg

/-- **Lemma 11**, p.23 (PDF p.24), with the factorization form of p.25.

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

With the hypotheses of Lemma 10 and any `L` with `LL⊤ = D̄`: the game (21) has optimum at most 1, that is,
some `∥x∥₂ ≤ 1` has `h(x, y) ≤ 1` for all `∥y∥_q ≤ 1`; and if `∥x̃∥₂ ≤ 1` and `h(x̃, y) ≤ ξ` for all
`∥y∥_q ≤ 1`, for some `ξ ≥ 1`, then `ũ := L^{−⊤}(ρx̃ + ½L^{−1}h̄)` is feasible for (19) with `∥Āũ∥_p ≤ ξ`.

**Formalization Note.** `L = D̄^{1/2}` is the printed form and a Cholesky factor is the form of p.25. `q`
is `conjExp p`. -/
theorem lemma_11 {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (hA : Function.Injective A.mulVec)
    (D : Matrix (Fin k) (Fin k) ℝ) (hD : D.PosSemidef) (h : Fin k → ℝ) (w : Fin n → ℝ) (p ζ : ℝ)
    (hp : 2 ≤ p) (hw : IsLewisOver A (1 / p) w) (hζ₁ : ζ / 2 < phiStar h D A p)
    (hζ₂ : phiStar h D A p ≤ ζ) (L : Matrix (Fin k) (Fin k) ℝ)
    (hL : L * Lᵀ = scaledD A D h w p ζ) :
    (∃ x : Fin k → ℝ, l2Norm x ≤ 1 ∧ ∀ y : Fin n → ℝ, lpNorm (conjExp p) y ≤ 1 →
      gameObj (gameM (scaledA A p ζ) L (scaledH h ζ)) (gameC (scaledA A p ζ) L (scaledH h ζ)) x y
        ≤ 1) ∧
    (∀ (ξ : ℝ) (xt : Fin k → ℝ), 1 ≤ ξ → l2Norm xt ≤ 1 →
      (∀ y : Fin n → ℝ, lpNorm (conjExp p) y ≤ 1 →
        gameObj (gameM (scaledA A p ζ) L (scaledH h ζ)) (gameC (scaledA A p ζ) L (scaledH h ζ))
          xt y ≤ ξ) →
      scaledConstraint (scaledH h ζ) (scaledD A D h w p ζ) (recover L (scaledH h ζ) xt)
        ≤ -(1 / 8) ∧
      lpNorm p (scaledA A p ζ *ᵥ recover L (scaledH h ζ) xt) ≤ ξ) := by sorry

end PNormReg
