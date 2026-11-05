-- Prove2me | Theorems.Thm_TwoStageMatch_type_I_feasibility
-- name    : TwoStageMatch.type_I_feasibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:05.650191+00:00
-- url     : https://prove2.me/theorems/f58cb725-344e-4f58-8acc-596e24c86113
-- title:
--   (6): Type I dual constraints hold with factor $3/4$
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone (non-decreasing) and strictly convex. Suppose all weights are positive, let $(x^*,\rho)$ be a run of Algorithm 1, write $y^*_j=\sum_{i\in N(j)}x^*_{ij}$, fix a realization $\tilde D_2=A$ and a first-stage matching $M_1$ with matched supplies $S_1$, let $(\hat\alpha,\hat\beta)$ be an optimal dual of the residual matching LP on $G[A,S\setminus S_1]$, and let $(\alpha,\beta)$ be the dual assignment of p.15. Then for every edge $(i,j)\in E$ with $i\in D^{(l)}\subseteq D_1$ and $j\in S^{(l')}$,
--   $$\alpha_i+\beta_j\ge c^{(l)}+w_jy_j^{*2}\ge c^{(l')}+w_jy_j^{*2}=w_j(1-y^*_j)+w_jy_j^{*2}\ge\frac34w_j .$$
--   In particular $\mathbb E_{M_1}[\alpha_i+\beta_j]\ge\frac34w_j$.
--
--   Differences from the source:
--   - encoding: 𝒫^g and its optimal solution, with 1/w_j in the objective → hypothesis w_j > 0 for every supply j; reason: the paper's 𝒫^g divides by w_j and is undefined when some w_j = 0; the hypothesis excludes only that undefined case
--   - reading: Algorithm 1 (an optimal x* of 𝒫^g and M₁ sampled with marginals x*) → every run (x*, ρ): every optimal x* and every distribution ρ on first-stage matchings with marginals x*; reason: the paper fixes neither the minimizer nor the rounding; quantifying over all of them covers every choice
--   - generalization: the chain (6) for the sampled M₁ and its expectation → the chain (6) for every first-stage matching M₁, the expectation not written; reason: pointwise for every M₁ implies the paper's pointwise and expected bounds (ρ is supported on first-stage matchings)
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, proof of Theorem 1, p.15, eq. (6) (Type I edges)

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_DualAssignment

namespace TwoStageMatch

/-- **Type I dual constraints, (6)** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, proof of
Theorem 1, p.15). Let `g` be differentiable, monotone and strictly convex, let all weights be
positive, let `(x*, ρ)` be a run of Algorithm 1, fix a realization `D̃₂ = A` and a first-stage
matching `M₁` (supplies `S₁`), and let `(α̂, β̂)` be an optimal dual of the residual matching LP
on `G[A, S \ S₁]`. Then the dual assignment `(α, β)` of p.15 satisfies, for every edge
`(i, j) ∈ E` with `i ∈ D₁`,
`α_i + β_j ≥ c⁽ˡ⁾ + w_j y*_j² ≥ c⁽ˡ′⁾ + w_j y*_j² = w_j (1 − y*_j) + w_j y*_j² ≥ (3/4) w_j`
(pointwise in `M₁`, hence also in expectation). -/
theorem type_I_feasibility {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j) (r : Run I g) (A : Finset D₂)
    (M : Finset ((D₁ ⊕ D₂) × S)) (hM : IsFirstStageMatching I M)
    (αh : D₁ ⊕ D₂ → ℝ) (βh : S → ℝ)
    (hopt : IsDualFeasible I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) αh βh ∧
      dualObj (secondStage A) (Finset.univ \ matchedSupply M) αh βh =
        maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)) :
    ∀ i j, I.E (Sum.inl i) j →
      levelSlack I.w r.x (levelD r.x i) + I.w j * (load r.x j) ^ 2 ≤
          dualAlpha I r.x αh (Sum.inl i) + dualBeta I r.x M βh j ∧
        levelSlack I.w r.x (levelS r.x j) + I.w j * (load r.x j) ^ 2 ≤
          levelSlack I.w r.x (levelD r.x i) + I.w j * (load r.x j) ^ 2 ∧
        levelSlack I.w r.x (levelS r.x j) + I.w j * (load r.x j) ^ 2 =
          I.w j * (1 - load r.x j) + I.w j * (load r.x j) ^ 2 ∧
        (3 / 4 : ℝ) * I.w j ≤ I.w j * (1 - load r.x j) + I.w j * (load r.x j) ^ 2 := by sorry

end TwoStageMatch
