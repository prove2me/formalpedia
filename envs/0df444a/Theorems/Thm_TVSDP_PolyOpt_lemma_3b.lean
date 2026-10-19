-- Prove2me | Theorems.Thm_TVSDP_PolyOpt_lemma_3b
-- name    : TVSDP.PolyOpt.lemma_3b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:59.551124+00:00
-- url     : https://prove2.me/theorems/c76e3140-dd4d-495b-8559-c1d526c2fee6
-- title:
--   Lemma 3(b), p. 12 — $\sup_{t\in[0,1]}|a(t)\mathcal M_vx(t)-\mathcal M_v(a\cdot x)(t)|\to0$ for polynomial $a$
-- statement:
--   Let $a\in\mathbb R[t]$ be a polynomial and $x:[0,1]\to\mathbb R$ be measurable and bounded (the space $\mathbf L^1$ of the paper). Then
--
--   $$\sup_{t\in[0,1]}\bigl|a(t)\,\mathcal M_vx(t)-\mathcal M_v(a\cdot x)(t)\bigr|\;\longrightarrow\;0\qquad(v\to\infty),$$
--
--   where $a\cdot x$ is the function $s\mapsto a(s)x(s)$ and $\mathcal M_v$ is the mollifying operator of Definition 3.
--
--   The lemma says that mollification nearly commutes with multiplication by a polynomial, uniformly on $[0,1]$; it is how the paper compares the mollification of $\mathcal Fx$ with $\mathcal F$ applied to the mollification of $x$.
--
--   **Formalization Note** The uniform convergence is stated without a supremum: for every $\delta>0$, for all sufficiently large $v$, the difference is at most $\delta$ at every $t\in[0,1]$.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, p. 12, Lemma 3(b)

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Mollifier

namespace TVSDP.PolyOpt

open Filter

/-- Lemma 3(b), p. 12: for every polynomial `a` and every bounded measurable `x` (the space `L¹` of the
paper), `sup_{t ∈ [0,1]} |a(t) 𝓜_v x(t) - 𝓜_v(a · x)(t)| → 0` as `v → ∞`, stated as: for every
`δ > 0`, for all large `v`, the difference is at most `δ` at every `t ∈ [0,1]`. -/
theorem lemma_3b (a : Polynomial ℝ) (x : ℝ → ℝ) (hx : Measurable x)
    (hxb : ∃ M : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, |x t| ≤ M) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ v : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
      |a.eval t * Mv v x t - Mv v (fun s => a.eval s * x s) t| ≤ δ := by sorry

end TVSDP.PolyOpt
