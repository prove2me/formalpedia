-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_theorem_ec3
-- name    : TwoStageMatch.Supplement.theorem_ec3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:15:19.302948+00:00
-- url     : https://prove2.me/theorems/87c7b061-61bd-50f4-bd45-09967dad95a3
-- title:
--   Theorem EC.3: Algorithm 1 is $\min_{j\in S}(1-y_j+y_j^2)$-competitive against $\mathrm{OPT}_{\mathrm{offline}}$
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone increasing and strictly convex. On every weighted two-stage stochastic matching instance (supply weights $w_j\ge0$, probabilities $\pi_i\in[0,1]$) and for every run of Algorithm 1, let $y_j$ be the probability that supply $j$ is matched in the first stage. Then
--   $$\mathbb E\Big[\sum_{j\in S}w_j\mathbb 1\{j\text{ matched in }M_1\cup M_2\}\Big]\ \ge\ \Big(\min_{j\in S}\big(1-y_j+y_j^2\big)\Big)\cdot\mathrm{OPT}_{\mathrm{offline}}.$$
--
--   Since $1-y+y^2\ge3/4$ with equality only at $y=1/2$, this refines Theorem 1: the less random the first-stage matching, the closer Algorithm 1 is to the optimum offline.
--
--   **Formalization Note** The statement is given for every lower bound $c$ of $\{1-y_j+y_j^2\}_{j\in S}$, which is the bound for $c=\min_j(1-y_j+y_j^2)$ and is trivial when $S=\varnothing$.
--
--   Differences from the source:
--   - encoding: (min_{j∈S} 1 − y_j + y_j²)-competitive → for every run and every c ≤ 1 − y_j + y_j² for all j: value ≥ c·OPT_offline; reason: the ratio depends on the run; the statement for all lower bounds c is the statement for the minimum when S ≠ ∅, and when S = ∅ both sides vanish
--   - generalization: 𝒫^g with 1/w_j, undefined when some w_j = 0 → instances with w_j ≥ 0, the published objective dropping the term of a zero-weight supply (Lean's 1/0 = 0); reason: on positive weights it is the paper's program, so the statement specializes to the source; with zero weights, deleting the zero-weight supplies changes neither the run's value nor OPT_offline, the restricted x* is optimal for the restricted instance (its KKT multipliers carry over), and the minimum over all j is at most the minimum over the positive-weight ones
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Theorem EC.3, p.ec14

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1

namespace TwoStageMatch.Supplement

/-- **Theorem EC.3** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.ec14; proof sketched there).
For any differentiable, monotone increasing and strictly convex function `g : ℝ → ℝ`, suppose
`{y_j}_{j ∈ S}` is the probability that each supply vertex `j ∈ S` is matched in the first stage
in Algorithm 1; then Algorithm 1 is `(min_{j ∈ S} 1 − y_j + y_j²)`-competitive against the optimum
offline benchmark `OPT_offline`.

Stated per instance and per run (the ratio depends on both): on every instance (weights `w ≥ 0`,
probabilities `π ∈ [0, 1]`) and for every run `(x*, ρ)` of Algorithm 1, with
`y_j = Pr_{M₁ ∼ ρ}[j matched by M₁]`, every `c` with `c ≤ 1 − y_j + y_j²` for all `j ∈ S` satisfies
`value ≥ c · OPT_offline`.

**Formalization Note.** Quantifying over all lower bounds `c` of `{1 − y_j + y_j²}` is the
statement for `c = min_j (1 − y_j + y_j²)` when `S` is nonempty (and holds trivially for
`S = ∅`, where `OPT_offline = 0`). On an instance with a zero weight, the published objective of
`𝒫^g` drops that supply's term (`1/0 = 0`), as for the published Theorem 1. -/
theorem theorem_ec3 (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g)
    {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂]
    [DecidableEq S] (I : Instance D₁ D₂ S) (r : Run I g) (c : ℝ)
    (hc : ∀ j : S,
      c ≤ 1 - (∑ M, r.ρ M * (if j ∈ matchedSupply M then 1 else 0)) +
        (∑ M, r.ρ M * (if j ∈ matchedSupply M then 1 else 0)) ^ 2) :
    c * optOffline I ≤ r.value := by sorry

end TwoStageMatch.Supplement
