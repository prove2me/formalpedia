-- Prove2me | Theorems.Thm_PolyContract_theorem_3_3
-- name    : PolyContract.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:48:20.363719+00:00
-- url     : https://prove2.me/theorems/d8256b44-a798-4902-a619-8c4079234d9a
-- title:
--   Theorem 3.3 — level sets are maximal minimizers of $F_{\alpha,\theta}$
-- statement:
--   Let $(f,m,\beta)$ be a valid instance with quadratic costs. For all $\alpha\ge0$ and $\theta>0$, the level set $A_\theta(\alpha)=A_\theta(x^\star(\alpha))$ is the unique maximal minimizer of
--   $$F_{\alpha,\theta}(S)=f(S)-\alpha\,t(S)+\theta\,\beta^{-1}(S).$$
--
--   This connects the best response to submodular minimization.
--
--   Differences from the source: none.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem 3.3, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract

/-- **Theorem 3.3** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026,
sha256 18cfc0a5…, p.7). "For all `α ≥ 0`, `θ > 0`, the level set `A_θ(α)` is the unique maximal
minimizer of `F_{α,θ}`," where `A_θ(α) := A_θ(x⋆(α))` and
`F_{α,θ}(S) := f(S) − α t(S) + θ β⁻¹(S)`.

**Formalization Note** Valid instance with quadratic costs. The statement is made for every best
response at `α` (it is unique, §3 p.7). A maximal minimizer (it minimizes, and contains every
minimizer) is unique when it exists. -/
theorem theorem_3_3 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (I : QuadInstance ι) (hI : I.Valid) (α θ : ℝ) (hα : 0 ≤ α) (hθ : 0 < θ)
    (x : ι → ℝ) (hx : I.IsBestResponse α x) :
    IsMaximalMinimizer (I.Ffun α θ) (I.levelSet α x θ) := by sorry

end PolyContract
