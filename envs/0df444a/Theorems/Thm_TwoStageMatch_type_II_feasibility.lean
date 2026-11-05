-- Prove2me | Theorems.Thm_TwoStageMatch_type_II_feasibility
-- name    : TwoStageMatch.type_II_feasibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:13.031177+00:00
-- url     : https://prove2.me/theorems/199a36c9-9057-4ed9-bc48-9c56b937fccf
-- title:
--   (7): Type II dual constraints hold in expectation with factor $3/4$
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone (non-decreasing) and strictly convex. Suppose all weights are positive, let $(x^*,\rho)$ be a run of Algorithm 1, write $y^*_j=\sum_{i\in N(j)}x^*_{ij}$, and fix a realization $\tilde D_2=A$. For every first-stage matching $M_1$ (matched supplies $S_1$) let $(\hat\alpha,\hat\beta)(M_1)$ be an optimal dual of the residual matching LP on $G[A,S\setminus S_1]$ (dual feasible, with objective $\mathrm{Max\text{-}WeightMatch}^w(A,S\setminus S_1)$), and let $(\alpha,\beta)$ be the dual assignment of p.15. Then for every edge $(i,j)\in E$ with $i\in A$,
--   $$\mathbb E_{M_1}[\alpha_i+\beta_j]\ge\mathbb E_{M_1}\big[w_j\mathbb 1\{j\text{ is not matched in }M_1\}+w_jy_j^{*2}\big]=w_j(1-y^*_j)+w_jy_j^{*2}\ge\frac34w_j,$$
--   where $M_1\sim\rho$.
--
--   Differences from the source:
--   - encoding: 𝒫^g and its optimal solution, with 1/w_j in the objective → hypothesis w_j > 0 for every supply j; reason: the paper's 𝒫^g divides by w_j and is undefined when some w_j = 0; the hypothesis excludes only that undefined case
--   - reading: Algorithm 1 (an optimal x* of 𝒫^g and M₁ sampled with marginals x*) → every run (x*, ρ): every optimal x* and every distribution ρ on first-stage matchings with marginals x*; reason: the paper fixes neither the minimizer nor the rounding; quantifying over all of them covers every choice
--   - encoding: 𝔼_{M₁}[·] with M₁ sampled with marginals x* → Σ_M ρ(M)·(·) over all Finsets of edges, ρ supported on first-stage matchings; the first two steps of (7) merged into one inequality; reason: the expectation over the finite law ρ; the residual duals depend on M₁; the merged steps are unfolding the definition of (α, β) and β̂ ≥ 0
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, proof of Theorem 1, pp.15–16, eq. (7) (Type II edges)

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_DualAssignment

namespace TwoStageMatch

/-- **Type II dual constraints in expectation, (7)** (Feng, Niazadeh & Saberi,
arXiv:2210.11648v1, proof of Theorem 1, pp.15–16). Let `g` be differentiable, monotone and
strictly convex, let all weights be positive, let `(x*, ρ)` be a run of Algorithm 1 and fix a
realization `D̃₂ = A`. For every first-stage matching `M₁` let `(α̂, β̂)(M₁)` be an optimal dual of
the residual matching LP on `G[A, S \ S₁]`, and let `(α, β)` be the dual assignment of p.15. Then
for every edge `(i, j) ∈ E` with `i ∈ A`,
`𝔼_{M₁}[α_i + β_j] ≥ 𝔼_{M₁}[w_j 𝟙{j is not matched in M₁}] + w_j y*_j² = w_j (1 − y*_j) + w_j y*_j²
 ≥ (3/4) w_j`, where `M₁ ∼ ρ`. -/
theorem type_II_feasibility {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j) (r : Run I g) (A : Finset D₂)
    (αh : Finset ((D₁ ⊕ D₂) × S) → D₁ ⊕ D₂ → ℝ) (βh : Finset ((D₁ ⊕ D₂) × S) → S → ℝ)
    (hopt : ∀ M, IsFirstStageMatching I M →
      IsDualFeasible I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) (αh M) (βh M) ∧
      dualObj (secondStage A) (Finset.univ \ matchedSupply M) (αh M) (βh M) =
        maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)) :
    ∀ i ∈ A, ∀ j, I.E (Sum.inr i) j →
      ∑ M, r.ρ M * (I.w j * (if j ∈ Finset.univ \ matchedSupply M then 1 else 0) +
            I.w j * (load r.x j) ^ 2) ≤
          ∑ M, r.ρ M * (dualAlpha I r.x (αh M) (Sum.inr i) + dualBeta I r.x M (βh M) j) ∧
        ∑ M, r.ρ M * (I.w j * (if j ∈ Finset.univ \ matchedSupply M then 1 else 0) +
            I.w j * (load r.x j) ^ 2) =
          I.w j * (1 - load r.x j) + I.w j * (load r.x j) ^ 2 ∧
        (3 / 4 : ℝ) * I.w j ≤ I.w j * (1 - load r.x j) + I.w j * (load r.x j) ^ 2 := by sorry

end TwoStageMatch
