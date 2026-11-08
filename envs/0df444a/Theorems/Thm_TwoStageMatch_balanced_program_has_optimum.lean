-- Prove2me | Theorems.Thm_TwoStageMatch_balanced_program_has_optimum
-- name    : TwoStageMatch.balanced_program_has_optimum
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:32:42.394191+00:00
-- url     : https://prove2.me/theorems/66e33635-4e70-4bfa-ae52-90ca37ea0eca
-- title:
--   Algorithm 1, step 3: the program $\mathscr P^g$ has an optimal solution
-- statement:
--   Algorithm 1 begins by solving the convex program $\mathscr P^g$ (step 3, p.13). On every instance and for every continuous $g:\mathbb R\to\mathbb R$ (in particular for every differentiable $g$), $\mathscr P^g$ has an optimal solution: there is a feasible fractional first-stage matching $x^*$ with
--   $$\sum_{j\in S}\frac1{w_j}g\Big(w_j\Big(1-\sum_{i}x^*_{ij}\Big)\Big)\le\sum_{j\in S}\frac1{w_j}g\Big(w_j\Big(1-\sum_{i}x_{ij}\Big)\Big)\quad\text{for every feasible }x.$$
--
--   This makes step 3 of Algorithm 1 well defined; together with the rounding statement it shows that runs of Algorithm 1 exist, so the statements quantifying over runs are not vacuous.
--
--   Differences from the source:
--   - generalization: g differentiable, increasing and strictly convex → g continuous; reason: differentiable functions are continuous, so the statement specializes to the paper's class
--   - generalization: weights w_j ∈ ℝ≥0, with Algorithm 1 defined through 𝒫^g, which divides by w_j → every instance with w_j ≥ 0, where a supply of weight 0 contributes (1/0)·g(…) = 0 to the objective; reason: on instances with all w_j > 0 the Lean program is the paper's 𝒫^g, so the statement specializes to the paper's; zero-weight supplies can be deleted without changing any side of the bound (a minimizer restricted to the positive-weight supplies is a minimizer there, the restricted rounding has the restricted marginals, and zero-weight supplies add nothing to any matching weight)
--   - encoding: existence of x* is presupposed by step 3, not stated → an explicit existence statement; reason: the plan adds this milestone so that Algorithm 1 is not vacuous; it changes no instance
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, Algorithm 1, step 3, p.13 ("Solve convex program 𝒫^g to obtain {x*_ij}")

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1

namespace TwoStageMatch

/-- **Algorithm 1, step 3** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.13: "Solve convex
program 𝒫^g to obtain {x*_ij}"). The program `𝒫^g` of p.12 has an optimal solution on every
instance, for every continuous `g` (in particular for every differentiable `g`). The feasible set
is nonempty (it contains `0`) and compact, and the objective is continuous.

**Formalization Note.** `IsOptimal I g x` says that `x` is feasible and minimizes the objective
`Σ_j (1 / w_j) g(w_j (1 − Σ_i x_{ij}))` over the feasible set; a supply of weight `0` contributes
`0` (Lean's `1 / 0 = 0`). -/
theorem balanced_program_has_optimum {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hg : Continuous g) :
    ∃ x : D₁ → S → ℝ, IsOptimal I g x := by sorry

end TwoStageMatch
