-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_b_4
-- name    : PolyContract.Supplement.theorem_b_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:04:21.091314+00:00
-- url     : https://prove2.me/theorems/8eb5b48c-48a9-4c4e-bcff-441dcac5b24a
-- title:
--   Theorem B.4 — the marginals $\alpha\mapsto\rho_e(\alpha)$ are nondecreasing on $[0,\infty)$
-- statement:
--   Let $(f,m,\beta)$ be a valid instance with quadratic costs and let $x^\star(\alpha)$ be the best response. For every $e\in E$ the marginal
--   $$\rho_e(\alpha)=\alpha m_e-\beta_e x^\star_e(\alpha)$$
--   is nondecreasing on $[0,\infty)$: $\rho_e(\alpha)\le\rho_e(\alpha')$ whenever $0\le\alpha\le\alpha'$.
--
--   Monotone marginals make the level sets $A_\theta(\alpha)$ grow with the share.
--
--   Differences from the source:
--   - encoding: the marginal of the best response x⋆ → the marginals of any best responses x at α and x′ at α′; reason: the best response is unique (published milestone), so this is the same statement
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem B.4, App. B.1, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem B.4** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, App. B.1, p.21): for every `e ∈ E`, the marginal `α ↦ ρ_e(α) = α m_e − β_e x⋆_e(α)` is
nondecreasing on `[0, ∞)`.

**Formalization Note** The instance is a valid quadratic-cost instance; `x⋆(α)` and `x⋆(α′)` are
any best responses at the two shares (they are unique, published milestone
`PolyContract.bestResponse_existsUnique`). -/
theorem theorem_b_4 {ι : Type} [Fintype ι] [DecidableEq ι] (I : QuadInstance ι) (hI : I.Valid)
    (α α' : ℝ) (hα : 0 ≤ α) (hαα' : α ≤ α') (x x' : ι → ℝ) (hx : I.IsBestResponse α x)
    (hx' : I.IsBestResponse α' x') (e : ι) :
    I.marginal α x e ≤ I.marginal α' x' e := by sorry

end PolyContract.Supplement
