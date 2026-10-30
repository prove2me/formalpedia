-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_weak_duality_12
-- name    : PlotkinShmoysTardos.weak_duality_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:52:41.162498+00:00
-- url     : https://prove2.me/theorems/463a6259-a705-40f9-a63a-12b649c7d454
-- title:
--   (12) — weak duality $\lambda y^td\ge y^tAx-y^tb\ge C_{\mathcal G}(y)$ and $\lambda^*\ge C_{\mathcal G}(y)/y^td$
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b,d\in\mathbb R^m$ and $P\subseteq\mathbb R^n$. Let $(x,\lambda)$ be a feasible solution of
--   $$
--   \min(\lambda : Ax\le b+\lambda d \text{ and } x\in P), \tag{11}
--   $$
--   let $y\ge0$ be a dual solution, and let $x'\in P$ attain $C_{\mathcal G}(y)=\min(y^tAz-y^tb : z\in P)$. Then
--   $$
--   \lambda\,y^td\ \ge\ y^tAx-y^tb\ \ge\ C_{\mathcal G}(y). \tag{12}
--   $$
--   Moreover, if $y^td>0$ then $\lambda\ge C_{\mathcal G}(y)/y^td$; since this holds for every feasible $(x,\lambda)$, the optimal value $\lambda^*$ of (11) satisfies $\lambda^*\ge C_{\mathcal G}(y)/y^td$.
--
--   This weak-duality bound is the basis of the infeasibility certificate of Lemma 4.1.
--
--   Differences from the source:
--   - encoding: C_G(y) = min(yᵗAx' − yᵗb : x' ∈ P) → the value yᵗ(Ax' − b) at a given x' ∈ P that minimizes yᵗ(Az − b) over z ∈ P; reason: avoids an infimum with junk value 0 on unbounded sets; it is the paper's value whenever the minimum is attained, which the paper presupposes
--   - encoding: λ* ≥ C_G(y)/yᵗd, with λ* the optimal value of (11) → λ ≥ C_G(y)/yᵗd for every feasible (x, λ) of (11), when yᵗd > 0; reason: λ* is the infimum of the feasible λ, so the two are equivalent; yᵗd > 0 only excludes the division by zero the paper does not consider
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), §4, (12), p. 24

import Mathlib

namespace PlotkinShmoysTardos

/-- **The chain (12) and its consequence.** Plotkin–Shmoys–Tardos, TR 999 (1992), §4, (12),
p. 24: "`λ yᵗd ≥ yᵗA x − yᵗb ≥ C_G(y)`. (12) It follows that for any dual solution `y`,
`λ* ≥ C_G(y)/yᵗd`."
Let `x ∈ P` and `λ` with `A x ≤ b + λ d` (a feasible solution of (11)), let `y ≥ 0`, and let
`x' ∈ P` attain `C_G(y) = min(yᵗ(A z − b) : z ∈ P)`. Then
1. `yᵗ(A x − b) ≤ λ yᵗd`;
2. `C_G(y) = yᵗ(A x' − b) ≤ yᵗ(A x − b)`;
3. if `yᵗd > 0`, then `C_G(y)/yᵗd ≤ λ`; as `(x, λ)` ranges over all feasible solutions of (11),
   this is `λ* ≥ C_G(y)/yᵗd`. -/
theorem weak_duality_12 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (x : Fin n → ℝ) (hx : x ∈ P) (l : ℝ)
    (hfeas : ∀ i, A.mulVec x i ≤ b i + l * d i) (y : Fin m → ℝ) (hy : 0 ≤ y)
    (x' : Fin n → ℝ) (hx' : x' ∈ P)
    (hmin : ∀ z ∈ P, y ⬝ᵥ (A.mulVec x' - b) ≤ y ⬝ᵥ (A.mulVec z - b)) :
    y ⬝ᵥ (A.mulVec x - b) ≤ l * (y ⬝ᵥ d) ∧
      y ⬝ᵥ (A.mulVec x' - b) ≤ y ⬝ᵥ (A.mulVec x - b) ∧
      (0 < y ⬝ᵥ d → y ⬝ᵥ (A.mulVec x' - b) / (y ⬝ᵥ d) ≤ l) := by sorry

end PlotkinShmoysTardos
