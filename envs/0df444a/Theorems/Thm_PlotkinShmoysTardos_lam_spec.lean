-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_lam_spec
-- name    : PlotkinShmoysTardos.lam_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:51:47.730047+00:00
-- url     : https://prove2.me/theorems/9606804a-d434-4894-adbb-10e50db41a7c
-- title:
--   $\lambda(x)$ is the least $\lambda$ with $Ax\le b+\lambda d$
-- statement:
--   Let $A$ be a real $m\times n$ matrix with $m\ge1$, $b\in\mathbb R^m$, and $d\in\mathbb R^m$ with $d>0$. For every $x\in\mathbb R^n$, the value $\lambda(x)=\max_i (a_ix-b_i)/d_i$ satisfies $Ax\le b+\lambda(x)\,d$, and every $\lambda$ with $Ax\le b+\lambda d$ satisfies $\lambda\ge\lambda(x)$:
--   $$
--   \lambda(x)=\min\{\lambda : Ax\le b+\lambda d\}.
--   $$
--   This justifies the paper's notation $(x,\lambda)$ for a point together with its minimum value, used in Lemmas 4.2 and 4.3 and in Figure 4.
--
--   Differences from the source:
--   - generalization: for each x ∈ P → for every x ∈ ℝⁿ; reason: the identity does not involve P; it specializes to x ∈ P
--   - encoding: rows i = 1, …, m → m ≥ 1 ([NeZero m]); reason: maxᵢ over no rows is undefined in the paper; excludes only that undefined case
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), §4, p. 24 ("For each x ∈ P, there is a corresponding minimum value λ such that Ax ≤ b + λd"); Figure 4, p. 25 (λ₀ ← maxᵢ(aᵢx − bᵢ)/dᵢ)

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality

namespace PlotkinShmoysTardos

/-- **`λ(x)` is the least `λ` with `A x ≤ b + λ d`.** Plotkin–Shmoys–Tardos, TR 999 (1992), §4,
p. 24: "For each `x ∈ P`, there is a corresponding minimum value `λ` such that `A x ≤ b + λ d`";
Figure 4 (p. 25) computes it as `maxᵢ (aᵢ x − bᵢ)/dᵢ`. For `d > 0`, `lam A b d x` satisfies
`A x ≤ b + λ d`, and every `l` with `A x ≤ b + l d` is at least `lam A b d x`. -/
theorem lam_spec {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (x : Fin n → ℝ) :
    (∀ i, A.mulVec x i ≤ b i + lam A b d x * d i) ∧
      ∀ l : ℝ, (∀ i, A.mulVec x i ≤ b i + l * d i) → lam A b d x ≤ l := by sorry

end PlotkinShmoysTardos
