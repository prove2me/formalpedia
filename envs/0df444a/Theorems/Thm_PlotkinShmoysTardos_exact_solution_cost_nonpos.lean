-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_exact_solution_cost_nonpos
-- name    : PlotkinShmoysTardos.exact_solution_cost_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:53:11.189236+00:00
-- url     : https://prove2.me/theorems/54e7aed5-446f-4c59-8c4d-5e14e8001f1f
-- title:
--   §4 p. 24 — an exact solution forces $C_{\mathcal G}(y)\le0$
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$ and $P\subseteq\mathbb R^n$. Suppose the GENERAL problem has an exact solution, i.e. some $z\in P$ has $Az\le b$. Then for every dual solution $y\ge0$,
--   $$
--   C_{\mathcal G}(y)=\min(y^tAx'-y^tb : x'\in P)\le 0,
--   $$
--   where the minimum is taken at any point $x'\in P$ attaining it.
--
--   Together with Lemma 4.1 this is why a positive lower bound on $C_{\mathcal G}(y)$ certifies infeasibility.
--
--   Differences from the source:
--   - encoding: C_G(y) = min(yᵗAx' − yᵗb : x' ∈ P) → the value yᵗ(Ax' − b) at a given x' ∈ P that minimizes yᵗ(Az − b) over z ∈ P; reason: avoids an infimum with junk value 0 on unbounded sets; it is the paper's value whenever the minimum is attained, which the paper presupposes
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), §4, p. 24 ("Notice that if there exists an exact solution to the GENERAL problem, then C_G(y) ≤ 0 for each dual solution y.")

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General

namespace PlotkinShmoysTardos

/-- **An exact solution forces `C_G(y) ≤ 0`.** Plotkin–Shmoys–Tardos, TR 999 (1992), §4, p. 24:
"Notice that if there exists an exact solution to the GENERAL problem, then `C_G(y) ≤ 0` for each
dual solution `y`." If some `z ∈ P` has `A z ≤ b`, then for every `y ≥ 0` and every `x' ∈ P`
attaining `C_G(y) = min(yᵗ(A z − b) : z ∈ P)`, `C_G(y) = yᵗ(A x' − b) ≤ 0`. -/
theorem exact_solution_cost_nonpos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hex : ∃ z, IsExact A b P z) (y : Fin m → ℝ) (hy : 0 ≤ y)
    (x' : Fin n → ℝ) (hx' : x' ∈ P)
    (hmin : ∀ z ∈ P, y ⬝ᵥ (A.mulVec x' - b) ≤ y ⬝ᵥ (A.mulVec z - b)) :
    y ⬝ᵥ (A.mulVec x' - b) ≤ 0 := by sorry

end PlotkinShmoysTardos
