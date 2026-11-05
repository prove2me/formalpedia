-- Prove2me | Theorems.Thm_TwoStageMatch_theorem_1
-- name    : TwoStageMatch.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:50.663194+00:00
-- url     : https://prove2.me/theorems/c55811b2-a7c4-45dd-aa8f-e2cd840e24a7
-- title:
--   Theorem 1 — Weighted-Balanced-Utilization is $3/4$-competitive against $\mathsf{OPT}_{\mathrm{offline}}$ and $\mathsf{OPT}_{\mathrm{online}}$
-- statement:
--   For any differentiable, monotone increasing and strictly convex function $g:\mathbb R\to\mathbb R$,
--   $$\Gamma_{\text{weighted-matching}}(\text{Algorithm 1},\mathsf{OPT}_{\mathrm{online}})\ \ge\ \Gamma_{\text{weighted-matching}}(\text{Algorithm 1},\mathsf{OPT}_{\mathrm{offline}})\ \ge\ \frac34 .$$
--
--   The statement has two clauses.
--
--   1. On every finite instance (any bipartite graph between $D_1\cup D_2$ and $S$, weights $w_j\ge 0$, probabilities $\pi_i\in[0,1]$) and for every run $(x^*,\rho)$ of Algorithm 1 for $g$ (every optimal solution $x^*$ of $\mathscr P^g$ and every distribution of $M_1$ with marginals $x^*$),
--   $$\mathbb E\Big[\sum_{j\in S}w_j\mathbb 1\{j\text{ is matched in }M_1\cup M_2\}\Big]\ge\frac34\,\mathsf{OPT}_{\mathrm{offline}}\qquad\text{and}\qquad \mathsf{OPT}_{\mathrm{online}}\le\mathsf{OPT}_{\mathrm{offline}} .$$
--   2. For every selection $\sigma$ of runs of Algorithm 1 on the finite instances, with $\Gamma(\sigma,B)$ the infimum of $\mathrm{ALG}/B$ over the instances with $B>0$ (Definition 2),
--   $$\Gamma(\sigma,\mathsf{OPT}_{\mathrm{online}})\ge\Gamma(\sigma,\mathsf{OPT}_{\mathrm{offline}})\ge\frac34 .$$
--
--   Algorithm 1 commits to a first-stage matching without looking at the second-stage demands, yet loses at most a quarter of the omniscient optimum; by Proposition 1 of the paper the constant $3/4$ cannot be improved against $\mathsf{OPT}_{\mathrm{offline}}$.
--
--   **Formalization Note** "Monotone increasing" is `Monotone g` (non-decreasing, the reading the paper's proof uses on p.ec5; under strict convexity it is equivalent to strictly increasing). Clause 1 is per instance and carries no $0/0$ convention; clause 2 is the printed statement.
--
--   Differences from the source:
--   - generalization: weights w_j ∈ ℝ≥0, with Algorithm 1 defined through 𝒫^g, which divides by w_j → every instance with w_j ≥ 0, where a supply of weight 0 contributes (1/0)·g(…) = 0 to the objective; reason: on instances with all w_j > 0 the Lean program is the paper's 𝒫^g, so the statement specializes to the paper's; zero-weight supplies can be deleted without changing any side of the bound (a minimizer restricted to the positive-weight supplies is a minimizer there, the restricted rounding has the restricted marginals, and zero-weight supplies add nothing to any matching weight)
--   - generalization: instances ranging over all graphs, weights and probabilities in Definition 2 → clause 1 over arbitrary finite types D₁, D₂, S in any universe; clause 2 over instances on Fin n₁, Fin n₂, Fin m; reason: every finite instance is isomorphic to a Fin-indexed one, so clause 2 is Definition 2; clause 1 covers every such instance
--   - reading: the min in Definition 2 → the infimum of ALG / OPT over the instances with OPT > 0; reason: the ratio is undefined (0/0) when OPT = 0 and the minimum need not be attained; clause 1 states every ratio directly
--   - reading: Algorithm 1 (an optimal x* of 𝒫^g and M₁ sampled with marginals x*) → every run (x*, ρ): every optimal x* and every distribution ρ on first-stage matchings with marginals x*; in clause 2, every selection σ of one run per instance; reason: the paper fixes neither the minimizer nor the rounding; quantifying over all of them covers every choice
--   - encoding: the graph G = (D, S, E) with D = D₁ ∪ D₂, matchings, the law of D̃₂ → D = D₁ ⊕ D₂, edges as a relation, matchings as Finsets of edges, x : D₁ → S → ℝ vanishing off the edges, the law of D̃₂ as the product weight Π_{i∈A} π_i Π_{i∉A} (1 − π_i) on Finset D₂; reason: Lean conventions; same instances
--   - encoding: monotone increasing g → Monotone g; reason: the paper's proof (p.ec5) uses "g(.) is non-decreasing"; under strict convexity non-decreasing is equivalent to strictly increasing
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, Theorem 1, p.12 (proof pp.13–16; Lemma 1 proof pp.ec4–ec6 = PDF pp.41–43)

import Mathlib
import Definitions.Def_TwoStageMatch_CompetitiveRatio

universe u

namespace TwoStageMatch

/-- **Theorem 1** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.12; proof pp.13–16). For any
differentiable, monotone increasing and strictly convex function `g : ℝ → ℝ`,
`Γ_weighted-matching(Algorithm 1, OPT_online) ≥ Γ_weighted-matching(Algorithm 1, OPT_offline) ≥ 3/4`.

Stated in two clauses:
* (a) on every finite instance (any bipartite graph, weights `w ≥ 0`, probabilities `π ∈ [0, 1]`)
  and for every run `(x*, ρ)` of Algorithm 1 for `g` (every optimal `x*` of `𝒫^g`, every rounding
  with marginals `x*`), the expected weight is at least `(3/4) · OPT_offline`, and
  `OPT_online ≤ OPT_offline`;
* (b) for every selection `σ` of runs of Algorithm 1 on the finite instances,
  `Γ(σ, OPT_online) ≥ Γ(σ, OPT_offline) ≥ 3/4`, where `Γ` is the infimum of `ALG / OPT` over the
  instances with `OPT > 0` (Definition 2, p.10).

**Formalization Note.** "Monotone increasing" is `Monotone g` (the proof, p.ec5, uses "g(.) is
non-decreasing"; under strict convexity it is equivalent to strictly increasing). On an instance
with a zero weight the Lean objective drops that supply's term (`1 / 0 = 0`); on positive weights
it is the paper's `𝒫^g`. -/
theorem theorem_1 (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) :
    (∀ {D₁ D₂ S : Type u} [Fintype D₁] [Fintype D₂] [Fintype S]
      [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S) (r : Run I g),
        (3 / 4 : ℝ) * optOffline I ≤ r.value ∧ optOnline I ≤ optOffline I) ∧
    (∀ σ : Selection g,
      gamma σ FinInstance.optOffline ≤ gamma σ FinInstance.optOnline ∧
        (3 / 4 : ℝ) ≤ gamma σ FinInstance.optOffline) := by sorry

end TwoStageMatch
