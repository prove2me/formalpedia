-- Prove2me | Theorems.Thm_TVSDP_PolyOpt_proposition_1
-- name    : TVSDP.PolyOpt.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:56.401872+00:00
-- url     : https://prove2.me/theorems/87ebf6e1-6620-42f3-83d3-82fb2f0d4d99
-- title:
--   Proposition 1, p. 11 (first two sentences) — $\mathcal M_v f$ is continuous and $\int_0^1|\mathcal M_vf-f|\to0$
-- statement:
--   Let $f:[0,1]\to\mathbb R$ be measurable and bounded (the space $\mathbf L^1$ of the paper, i.e. $\mathbf L^n$ with $n=1$), and let $\mathcal M_v$ be the mollifying operators of Definition 3. Then for every $v\in\mathbb N$ the function $\mathcal M_v f$ is continuous, and
--
--   $$\int_0^1 |\mathcal M_v f(t)-f(t)|\,dt \;\longrightarrow\; 0 \qquad (v\to\infty).$$
--
--   The proof of Theorem 4 uses the first statement to obtain continuous solutions and the second to control the objective value of the mollified solution.
--
--   **Formalization Note** Only the first two sentences of Proposition 1 are stated. The third sentence of the printed proposition (for continuous $f$, $\sup_{t\in[0,1]}|\mathcal M_vf(t)-f(t)|\to0$) is false for the operator of Definition 3: for $f\equiv1$, $\mathcal M_v f(0)=1/2$ for all $v\ge1$. The bold $\mathbf L^1$ of the paper is the space of bounded measurable functions, not Lebesgue $L^1$.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, p. 11, Proposition 1 (first two sentences)

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Mollifier

namespace TVSDP.PolyOpt

open Filter Topology

/-- Proposition 1 (first two sentences), p. 11: for every bounded measurable `f` (the space `L¹` of
the paper, i.e. `L^n` with `n = 1`) and every `v ∈ ℕ`, `𝓜_v f` is continuous, and
`∫₀¹ |𝓜_v f(t) - f(t)| dt → 0` as `v → ∞`. -/
theorem proposition_1 (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ M : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ M) :
    (∀ v : ℕ, Continuous (Mv v f)) ∧
    Tendsto (fun v : ℕ => ∫ t in (0:ℝ)..1, |Mv v f t - f t|) atTop (𝓝 0) := by sorry

end TVSDP.PolyOpt
