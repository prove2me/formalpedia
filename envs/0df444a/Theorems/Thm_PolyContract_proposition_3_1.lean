-- Prove2me | Theorems.Thm_PolyContract_proposition_3_1
-- name    : PolyContract.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:48:47.051412+00:00
-- url     : https://prove2.me/theorems/4d980cee-baa6-4c3e-9359-b6fc46481213
-- title:
--   Proposition 3.1 — optimality of a best response via its level sets
-- statement:
--   Let $(f,m,\beta)$ be a valid instance with quadratic costs and let $\alpha\ge0$. A point $x\in P^{(+)}(f)$ is the best response to $\alpha$ if and only if $\rho(x)\ge0$ and every level set $A_\theta(x)$, $\theta>0$, is tight:
--   $$x(A_\theta(x))=f(A_\theta(x)).$$
--   In particular, $0\le x^\star_e(\alpha)\le\alpha t_e$ for all $e$.
--
--   This optimality criterion underlies water-filling and all later structural results on the best response.
--
--   Differences from the source: none.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Proposition 3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract

/-- **Proposition 3.1** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026,
sha256 18cfc0a5…, p.7). "A point `x ∈ P(+)(f)` is the best response to `α` if and only if
`ρ(x) ≥ 0` and every level set `A_θ(x)`, `θ > 0`, is tight, i.e., `x(A_θ(x)) = f(A_θ(x))`. In
particular, `0 ≤ x⋆_e(α) ≤ α t_e` for all `e`."

**Formalization Note** Valid instance with quadratic costs and a share `α ≥ 0` ("Fix `α ≥ 0`",
App. B.1, p.18). `ρ(x)` is `marginal` at `α`, and `A_θ(x)` is `levelSet`. The "in particular"
clause is stated for every best response. -/
theorem proposition_3_1 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (I : QuadInstance ι) (hI : I.Valid) (α : ℝ) (hα : 0 ≤ α) :
    (∀ x ∈ indepPoly I.f, I.IsBestResponse α x ↔
      (∀ e, 0 ≤ I.marginal α x e) ∧
        ∀ θ : ℝ, 0 < θ → setSum x (I.levelSet α x θ) = I.f (I.levelSet α x θ)) ∧
    ∀ x, I.IsBestResponse α x → ∀ e, 0 ≤ x e ∧ x e ≤ α * I.t e := by sorry

end PolyContract
