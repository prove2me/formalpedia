-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_lemma_4_1
-- name    : PlotkinShmoysTardos.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:53:30.753019+00:00
-- url     : https://prove2.me/theorems/5640ab3f-ece4-4433-b9d0-eb3aee33e572
-- title:
--   Lemma 4.1 — G1, G2 and $\lambda>0$ certify that no exact solution exists
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $d\in\mathbb R^m$ with $d>0$, and $P\subseteq\mathbb R^n$. Let $x\in P$ and $\lambda$ satisfy $Ax\le b+\lambda d$, and let $y\ge 0$, $y\ne0$, be a dual solution. If $(x,\lambda,y)$ satisfies the relaxed optimality conditions
--   $$
--   \lambda\,y^td\le 4\,y^t(Ax-b)\quad(\mathcal G1),\qquad y^t(Ax-b)-C_{\mathcal G}(y)\le\tfrac{\lambda}{5}\,y^td\quad(\mathcal G2),
--   $$
--   and $\lambda>0$, then the GENERAL problem has no exact solution: no $z\in P$ satisfies $Az\le b$.
--
--   This lemma is the infeasibility certificate used by the relaxed decision procedure of Theorem 4.5.
--
--   Differences from the source:
--   - generalization: (x, λ) with λ the minimum value corresponding to x → any λ with Ax ≤ b + λd; reason: the minimum value is one such λ, so the paper's case is included
--   - generalization: G2 with C_G(y) = min(yᵗAx' − yᵗb : x' ∈ P) → G2 required against every competitor x' ∈ P (no attainment of the minimum assumed); reason: identical to the paper's G2 when the minimum is attained; the Lean also covers sets P where it is not
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), Lemma 4.1, p. 25

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality

namespace PlotkinShmoysTardos

/-- **Lemma 4.1.** Plotkin–Shmoys–Tardos, TR 999 (1992), p. 25: "Suppose that `(x, λ)` and
`y ≠ 0` are feasible primal and dual solutions that satisfy the relaxed optimality conditions G1
and G2, and `λ > 0`. Then there does not exist an exact solution to the GENERAL problem."
Here `d > 0`, `x ∈ P` with `A x ≤ b + λ d`, `y ≥ 0`, `y ≠ 0`, (G1) and (G2) hold for `(x, λ, y)`
and `λ > 0`; the conclusion is that no `z ∈ P` has `A z ≤ b`. -/
theorem lemma_4_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hd : ∀ i, 0 < d i) (x : Fin n → ℝ) (hx : x ∈ P) (l : ℝ)
    (hfeas : ∀ i, A.mulVec x i ≤ b i + l * d i) (y : Fin m → ℝ) (hy : 0 ≤ y) (hy0 : y ≠ 0)
    (hG1 : G1 A b d x l y) (hG2 : G2 A b d P x l y) (hl : 0 < l) :
    ¬ ∃ z, IsExact A b P z := by sorry

end PlotkinShmoysTardos
