-- Prove2me | Theorems.Thm_TVSDP_PolyOpt_F_lipschitz_sup
-- name    : TVSDP.PolyOpt.F_lipschitz_sup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:07.48009+00:00
-- url     : https://prove2.me/theorems/e5fccd66-c2e0-40b6-8e1a-01167c6756f3
-- title:
--   Proof of Theorem 4, pp. 13–14 — $\sup_t\|\mathcal Fx(t)-\mathcal Fy(t)\|\le C\sup_t\|x(t)-y(t)\|_\infty$, $C=\sup_{t,s}\sum_i\|A_i(t)\|+\|D_i(t,s)\|$
-- statement:
--   Consider a TV-SDP with polynomial data $A_0,\dots,A_n$, $D_1,\dots,D_n$ and operator $\mathcal F$. Let $x,y\in\mathbf L^n$, let $C$ be a constant with
--
--   $$\sum_{i=1}^n\bigl(\|A_i(t)\|+\|D_i(t,s)\|\bigr)\le C\qquad\text{for all } t,s\in[0,1],$$
--
--   and let $M$ be a constant with $\|x(s)-y(s)\|_\infty\le M$ for all $s\in[0,1]$. Then
--
--   $$\|\mathcal Fx(t)-\mathcal Fy(t)\|\le C\,M\qquad\text{for every } t\in[0,1].$$
--
--   Taking the least such constants, $\sup_{t\in[0,1]}\|\mathcal Fx(t)-\mathcal Fy(t)\|\le C\sup_{t\in[0,1]}\|x(t)-y(t)\|_\infty$ with $C=\sup_{t,s\in[0,1]}\sum_i(\|A_i(t)\|+\|D_i(t,s)\|)$. In the proof of Theorem 4 this turns uniform polynomial approximation of a continuous strictly feasible solution into uniform approximation of the constraint matrix.
--
--   **Formalization Note** The printed constant is $C=\sup_{t,s\in[0,1]}\sum_i\|A_i(t)\|+\|D_i(s,t)\|$, with the arguments of $D_i$ swapped; with that constant the inequality fails (for $n=m=1$, $A_1(t)=t$, $D_1(t,s)=t(1-s)$ and $x-y\equiv1$, the left side at $t=1$ is $3/2$ and the printed constant is $1$). The statement uses $D_i(t,s)$, the kernel as it appears in $\mathcal F$. The matrix norm is the entrywise maximum $\max_{j,k}|X_{jk}|$ (the page allows any matrix norm) and $\|\cdot\|_\infty$ is the maximum norm on $\mathbb R^n$. The statement is for arbitrary $x,y\in\mathbf L^n$, not only for the mollified solution and its polynomial approximant.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, pp. 13–14, proof of Theorem 4, last display of p. 13 and the definition of C on p. 14

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Setting

namespace TVSDP.PolyOpt

attribute [local instance] Matrix.normedAddCommGroup

/-- Proof of Theorem 4, pp. 13–14 (with the corrected constant): for `x, y ∈ L^n`, if
`C ≥ sup_{t,s ∈ [0,1]} ∑ᵢ (‖Aᵢ(t)‖ + ‖Dᵢ(t,s)‖)` and `M ≥ sup_{s ∈ [0,1]} ‖x(s) - y(s)‖_∞`, then
`‖𝓕x(t) - 𝓕y(t)‖ ≤ C M` for every `t ∈ [0,1]` (entrywise sup norm on matrices). -/
theorem F_lipschitz_sup {n m : ℕ} (P : Data n m) (x y : ℝ → Fin n → ℝ)
    (hx : x ∈ Ln n) (hy : y ∈ Ln n) (C M : ℝ)
    (hC : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1,
      ∑ i : Fin n, (‖evalMat (P.A i.succ) t‖ + ‖evalMat₂ (P.D i) t s‖) ≤ C)
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖x s - y s‖ ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ‖F P x t - F P y t‖ ≤ C * M := by sorry

end TVSDP.PolyOpt
