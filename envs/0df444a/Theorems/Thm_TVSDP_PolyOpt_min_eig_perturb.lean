-- Prove2me | Theorems.Thm_TVSDP_PolyOpt_min_eig_perturb
-- name    : TVSDP.PolyOpt.min_eig_perturb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:21.029382+00:00
-- url     : https://prove2.me/theorems/d3e60f1a-e138-4406-b304-04e9d2c799ad
-- title:
--   Proof of Theorem 4, p. 13 — minimum-eigenvalue step: $G(t)\succeq\beta I$ and $\sup_t\|G(t)-H_v(t)\|\to0$ give $H_v(t)\succeq\frac{\beta}{2}I$ for large $v$
-- statement:
--   Let $\beta>0$, let $G:[0,1]\to\mathbb R^{m\times m}$ satisfy $G(t)\succeq\beta I$ for every $t\in[0,1]$, and let $H_v:[0,1]\to\mathbb R^{m\times m}$, $v\in\mathbb N$, be symmetric for every $t\in[0,1]$ with
--
--   $$\sup_{t\in[0,1]}\|G(t)-H_v(t)\|\longrightarrow0\qquad(v\to\infty).$$
--
--   Then, for all sufficiently large $v$,
--
--   $$H_v(t)\succeq\frac{\beta}{2}\,I\qquad\text{for every } t\in[0,1].$$
--
--   In the proof of Theorem 4 this is the step "by continuity of the minimum eigenvalue function", applied to $G=\mathcal M_v\mathcal Fx^{\lambda,\varepsilon}$ and $H_v=\mathcal Fx^{v,\lambda,\varepsilon}$; it is also used again for the polynomial approximants.
--
--   **Formalization Note** The matrix norm is the entrywise maximum $\|X\|=\max_{i,j}|X_{ij}|$; the page allows any matrix norm, and all norms on $\mathbb R^{m\times m}$ are equivalent. The uniform convergence is stated as: for every $\delta>0$, for all large $v$, $\|G(t)-H_v(t)\|\le\delta$ at every $t\in[0,1]$. $X\succeq\beta I$ is positive semidefiniteness of $X-\beta I$ (which includes symmetry of $G(t)$).
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, p. 13, proof of Theorem 4, third paragraph

import Mathlib

namespace TVSDP.PolyOpt

open Filter

attribute [local instance] Matrix.normedAddCommGroup

/-- Proof of Theorem 4, p. 13 (minimum-eigenvalue step): if `G(t) ⪰ βI` for every `t ∈ [0,1]` with
`β > 0`, the matrices `H_v(t)` are symmetric, and `sup_{t ∈ [0,1]} ‖G(t) - H_v(t)‖ → 0` as `v → ∞`
(entrywise sup norm), then `H_v(t) ⪰ (β/2) I` for every `t ∈ [0,1]` once `v` is large enough. -/
theorem min_eig_perturb {m : ℕ} (β : ℝ) (hβ : 0 < β) (G : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (H : ℕ → ℝ → Matrix (Fin m) (Fin m) ℝ)
    (hG : ∀ t ∈ Set.Icc (0:ℝ) 1, (G t - β • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (hH : ∀ v : ℕ, ∀ t ∈ Set.Icc (0:ℝ) 1, (H v t).IsSymm)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ v : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1, ‖G t - H v t‖ ≤ δ) :
    ∀ᶠ v : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (H v t - (β / 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by sorry

end TVSDP.PolyOpt
