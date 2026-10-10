-- Prove2me | Theorems.Thm_WassMMSE_FW_eq_6_9
-- name    : WassMMSE.FW.eq_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:07.333958+00:00
-- url     : https://prove2.me/theorems/110bc069-d715-47ec-8feb-e8ff988ec605
-- title:
--   (6.9), p. 25 — under β-smoothness, f(s + ηd) ≤ f(s) − ηg + (η²β/2)‖d‖² for η ∈ [0, 1], and g ≥ 0
-- statement:
--   Let $\mathcal S=\times_k\mathcal S^{[k]}$ be a product of convex compact sets, let $f$ be convex on $\mathcal S$ and differentiable at its points, and let $F$ be an inexact oracle with precision $\delta\in[0,1]$ in the sense of (6.2). Assume that $f$ is $\beta$-smooth on $\mathcal S$ (Assumption 6.1 (i)). For $s\in\mathcal S$ write $d=F(s)-s$ for the search direction and $g=-d^\top\nabla f(s)$ for the surrogate duality gap. Then $g\ge0$ and
--
--   $$f(s+\eta d)\le f(s)-\eta g+\frac{\eta^2\beta}{2}\|d\|^2\qquad\forall\eta\in[0,1].$$
--
--   This quadratic upper bound along the Frank-Wolfe segment is what makes the line search of Algorithm 1 terminate.
--
--   **Formalization Note** The page remarks that (6.9) "holds in fact for all $\eta\in\mathbb R$"; that remark needs $f$ to be smooth beyond $\mathcal S$ and is not part of the statement.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 25, (6.9), proof of Theorem 6.2

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- (6.9), proof of Theorem 6.2, p. 25: under Assumption 6.1 (i), for every `s ∈ 𝒮`, with
`d = F(s) − s` and `g = −dᵀ∇f(s)`, the gap is nonnegative and
`f(s + ηd) ≤ f(s) − ηg + (η²β/2)‖d‖²` for all `η ∈ [0, 1]`. -/
theorem eq_6_9
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {β : ℝ} (hβ : IsSmoothOn S f β) {s : BlockSpace K d} (hs : s ∈ S) :
    0 ≤ fwGap f F s ∧
      ∀ η ∈ Set.Icc (0 : ℝ) 1,
        f (s + η • fwDirection F s)
          ≤ f s - η * fwGap f F s + η ^ 2 * β / 2 * ‖fwDirection F s‖ ^ 2 := by sorry

end WassMMSE.FW
