-- Prove2me | Theorems.Thm_TwoStageMatch_rounding_exists
-- name    : TwoStageMatch.rounding_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:10.987844+00:00
-- url     : https://prove2.me/theorems/ec7d9862-dcc1-46bc-8d10-ae3ecd6de813
-- title:
--   Rounding with exact marginals (4): every fractional first-stage matching is a mixture of matchings
-- statement:
--   For every instance and every feasible point $x$ of $\mathscr P^g$ (a fractional matching of $G[D_1,S]$), there is a probability distribution $\rho$ on matchings of $G[D_1,S]$ such that
--   $$\Pr_{M_1\sim\rho}[(i,j)\in M_1]=x_{ij}\qquad\text{for every } i\in D_1,\ j\in S,\ (i,j)\in E .$$
--
--   This is the step "because of the integrality of the bipartite matching polytope, the fractional matching $\{x^*_{ij}\}$ can be written down as a convex combination of integral bipartite matchings in $G[D_1,S]$" (p.12), which makes step 4 of Algorithm 1 possible.
--
--   Differences from the source:
--   - generalization: the optimal solution {x*_ij} of 𝒫^g → every feasible point x of 𝒫^g; reason: the decomposition does not use optimality; the paper's case is x = x*
--   - encoding: a convex combination of integral bipartite matchings → a nonnegative weight ρ on Finsets of edges, summing to 1 and supported on first-stage matchings, with the edge marginals (4); reason: same objects
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, §3.1.1, p.12, eq. (4) and the sentence after it

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1

namespace TwoStageMatch

/-- **Sampling rule (4)** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.12: "because of the
integrality of the bipartite matching polytope (Schrijver 2003), the fractional matching {x*_ij}
can be written down as a convex combination of integral bipartite matchings in G[D₁, S]").
Every feasible point `x` of `𝒫^g` is the edge-marginal vector of a probability distribution on
first-stage matchings: there is a probability weight `ρ` on matchings of `G[D₁, S]` with
`Pr[(i, j) ∈ M₁] = x_{ij}` for every first-stage edge `(i, j)`.

With `balanced_program_has_optimum` this shows that a run of Algorithm 1 exists on every
instance. -/
theorem rounding_exists {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (hx : IsFeasible I x) :
    ∃ ρ : Finset ((D₁ ⊕ D₂) × S) → ℝ, IsRounding I x ρ := by sorry

end TwoStageMatch
