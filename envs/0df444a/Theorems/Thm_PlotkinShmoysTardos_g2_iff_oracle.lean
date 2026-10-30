-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_g2_iff_oracle
-- name    : PlotkinShmoysTardos.g2_iff_oracle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:52:26.26599+00:00
-- url     : https://prove2.me/theorems/102ad661-26ea-4312-8bd1-b1be52484e70
-- title:
--   G2 can be tested at the point returned by subroutine (10)
-- statement:
--   Let $O$ be a subroutine (10) for $P$ and $A$, let $y\ge0$, let $x\in\mathbb R^n$ and $\lambda\in\mathbb R$. Then condition G2 holds for $(x,\lambda,y)$ if and only if
--   $$
--   y^t(Ax-b)-y^t(A\,O(y)-b)\le\frac{\lambda}{5}\,y^td .
--   $$
--   That is, $C_{\mathcal G}(y)$ is the cost of the point $O(y)$ for the costs $y^tA$, shifted by $y^tb$. This is how IMPROVE-GENERAL evaluates its loop test with one call to the subroutine; the paper uses "the point $\tilde x\in P$ that attains the minimum $C_{\mathcal G}(y)$".
--
--   Differences from the source:
--   - encoding: C_G(y) = min(yᵗAx' − yᵗb : x' ∈ P) → the value yᵗ(Ax' − b) at a given x' ∈ P that minimizes yᵗ(Az − b) over z ∈ P; reason: avoids an infimum with junk value 0 on unbounded sets; it is the paper's value whenever the minimum is attained, which the paper presupposes
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), §4, p. 24 (C_G(y) = min(yᵗAx − yᵗb : x ∈ P)); p. 25 ("we use the point x̃ ∈ P that attains the minimum C_G(y)")

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality

namespace PlotkinShmoysTardos

/-- **`C_G(y)` is the cost of the subroutine's point.** Plotkin–Shmoys–Tardos, TR 999 (1992), §4,
pp. 24–25: `C_G(y) = min(yᵗA x − yᵗb : x ∈ P)`, and IMPROVE-GENERAL uses "the point `x̃ ∈ P` that
attains the minimum `C_G(y)`", found by subroutine (10). For a subroutine `O` meeting the spec of
(10) and `y ≥ 0`, condition (G2) for `(x, l, y)` holds exactly when it holds against the
subroutine's point: `yᵗ(A x − b) − yᵗ(A O(y) − b) ≤ (l/5) yᵗd`. -/
theorem g2_iff_oracle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (O : (Fin m → ℝ) → (Fin n → ℝ)) (hO : IsMinOracle A P O)
    (x : Fin n → ℝ) (l : ℝ) (y : Fin m → ℝ) (hy : 0 ≤ y) :
    G2 A b d P x l y ↔
      y ⬝ᵥ (A.mulVec x - b) - y ⬝ᵥ (A.mulVec (O y) - b) ≤ l / 5 * (y ⬝ᵥ d) := by sorry

end PlotkinShmoysTardos
