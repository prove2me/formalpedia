-- Prove2me | Theorems.Thm_TwoStageMatch_proposition_ec1
-- name    : TwoStageMatch.proposition_ec1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:06.849605+00:00
-- url     : https://prove2.me/theorems/49c54689-babb-4721-9ca3-5a6881941a49
-- title:
--   Proposition EC.1 — strong duality and KKT conditions for $\mathscr P^g$
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone (non-decreasing) and strictly convex. Suppose all weights are positive, and let $x^*$ be an optimal solution of $\mathscr P^g$, with Lagrangian $\mathcal L^g$ (Definition EC.1). Then:
--
--   1. Strong duality:
--   $$\min_x\max_{\lambda,\theta,\gamma\ge0}\mathcal L^g(x,\lambda,\theta,\gamma)=\max_{\lambda,\theta,\gamma\ge0}\min_x\mathcal L^g(x,\lambda,\theta,\gamma)=\max_{\lambda,\theta,\gamma\ge0}\mathcal L^g(x^*,\lambda,\theta,\gamma),$$
--   and both maxima are attained (the minimum is attained at $x^*$ by the last equality).
--   2. If $\lambda^*,\theta^*,\gamma^*\ge 0$ attain the max–min, then for every $i\in D_1$, $j\in S$ with $(i,j)\in E$:
--      - (Stationarity) $\dfrac{\partial\mathcal L^g(x^*,\lambda^*,\theta^*,\gamma^*)}{\partial x_{ij}}=-g'\Big(w_j\Big(1-\sum_{i'\in N(j)}x^*_{i'j}\Big)\Big)+\lambda^*_i+\theta^*_j-\gamma^*_{ij}=0$;
--      - (Dual feasibility) $\lambda^*_i\ge0$, $\theta^*_j\ge0$, $\gamma^*_{ij}\ge0$;
--      - (Complementary slackness) $\gamma^*_{ij}=0$ or ($\gamma^*_{ij}>0$ and $x^*_{ij}=0$); $\lambda^*_i=0$ or ($\lambda^*_i>0$ and $\sum_{j\in N(i)}x^*_{ij}=1$); $\theta^*_j=0$ or ($\theta^*_j>0$ and $\sum_{i\in N(j)}x^*_{ij}=1$).
--
--   These are the ingredients of the proof of the structural decomposition (Lemma 1).
--
--   **Formalization Note** The min–max values are extended reals; the derivative is written out with $g'$ = `deriv g`, which is $\partial\mathcal L^g/\partial x_{ij}$ because $(1/w_j)\,w_j=1$.
--
--   Differences from the source:
--   - encoding: 𝒫^g and its optimal solution, with 1/w_j in the objective → hypothesis w_j > 0 for every supply j; reason: the paper's 𝒫^g divides by w_j and is undefined when some w_j = 0; the hypothesis excludes only that undefined case
--   - reading: the optimal solution x* of 𝒫^g → every optimal solution x*; reason: 𝒫^g need not have a unique minimizer in x (only the loads y* are pinned down); the claim is made for each
--   - reading: max over (λ, θ, γ) with dual feasibility λ*, θ*, γ* ≥ 0 listed as a conclusion → the maxima range over λ, θ, γ ≥ 0 (dual feasibility of a maximizer is then immediate); reason: the standard Lagrangian dual of inequality constraints; with free signs max_λ 𝓛^g is +∞ off the faces where every constraint is tight and the min–max would not be 𝒫^g
--   - encoding: min_x max 𝓛^g = max min_x 𝓛^g = max 𝓛^g(x*, ·), with min and max → ⨅/⨆ in EReal, with the attainment of both maxima stated explicitly; x ranges over D₁ → S → ℝ and only edge coordinates enter 𝓛^g; reason: the values may be ±∞ for infeasible x; same meaning
--   - encoding: ∂𝓛^g(x*, λ*, θ*, γ*)/∂x_ij = 0 → −deriv g (w_j (1 − Σ_{i'∈N(j)} x*_{i'j})) + λ*_i + θ*_j − γ*_ij = 0; reason: the partial derivative computed explicitly ((1/w_j)·w_j = 1 for w_j > 0)
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, Appendix EC.2.2, Proposition EC.1, p.ec5 (PDF p.42)

import Mathlib
import Definitions.Def_TwoStageMatch_Lagrangian

namespace TwoStageMatch

/-- **Proposition EC.1 (Strong duality/KKT conditions)** (Feng, Niazadeh & Saberi,
arXiv:2210.11648v1, p.ec5). Let `g` be differentiable, monotone and strictly convex, let all
weights be positive, and let `x*` be an optimal solution of `𝒫^g`. Then
1. `min_x max_{λ,θ,γ ≥ 0} 𝓛^g = max_{λ,θ,γ ≥ 0} min_x 𝓛^g = max_{λ,θ,γ ≥ 0} 𝓛^g(x*, ·)`, and both
   maxima are attained (the minimum over `x` is attained at `x*` by the last equality);
2. every multiplier vector `(λ*, θ*, γ*) ≥ 0` solving the max–min satisfies, for every
   first-stage edge `(i, j) ∈ E`:
   * stationarity `∂𝓛^g(x*, λ*, θ*, γ*)/∂x_{ij} = −g′(w_j (1 − Σ_{i' ∈ N(j)} x*_{i'j})) + λ*_i + θ*_j
     − γ*_{ij} = 0`;
   * dual feasibility `λ*_i ≥ 0`, `θ*_j ≥ 0`, `γ*_{ij} ≥ 0`;
   * complementary slackness `γ*_{ij} = 0 ∨ (γ*_{ij} > 0 ∧ x*_{ij} = 0)`,
     `λ*_i = 0 ∨ (λ*_i > 0 ∧ Σ_{j ∈ N(i)} x*_{ij} = 1)`,
     `θ*_j = 0 ∨ (θ*_j > 0 ∧ Σ_{i ∈ N(j)} x*_{ij} = 1)`.

**Formalization Note.** The min–max values are in `EReal` (`primalValue` is `+∞` at an
infeasible `x`). The partial derivative is written out explicitly with `deriv g`; it is
`∂𝓛^g/∂x_{ij}` because `(1/w_j) · w_j = 1` for `w_j > 0`. The load sums use the neighbour sets
(`supplyLoad`, `demandLoad`), which agree with `Σ_i x*_{ij}`, `Σ_j x*_{ij}` for a feasible `x*`. -/
theorem proposition_ec1 {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j)
    (x : D₁ → S → ℝ) (hx : IsOptimal I g x) :
    (minimax I g = maximin I g ∧
      maximin I g = ⨆ (m : Multipliers D₁ S) (_ : m.Nonneg), (lagrangian I g x m : EReal)) ∧
    (∃ m : Multipliers D₁ S, m.Nonneg ∧ dualFunction I g m = maximin I g) ∧
    (∃ m : Multipliers D₁ S, m.Nonneg ∧
      (lagrangian I g x m : EReal) =
        ⨆ (m' : Multipliers D₁ S) (_ : m'.Nonneg), (lagrangian I g x m' : EReal)) ∧
    ∀ m : Multipliers D₁ S, m.Nonneg → dualFunction I g m = maximin I g →
      ∀ i j, I.E (Sum.inl i) j →
        (-deriv g (I.w j * (1 - supplyLoad I x j)) + m.lam i + m.theta j - m.gam i j = 0) ∧
        (0 ≤ m.lam i ∧ 0 ≤ m.theta j ∧ 0 ≤ m.gam i j) ∧
        (m.gam i j = 0 ∨ (0 < m.gam i j ∧ x i j = 0)) ∧
        (m.lam i = 0 ∨ (0 < m.lam i ∧ demandLoad I x i = 1)) ∧
        (m.theta j = 0 ∨ (0 < m.theta j ∧ supplyLoad I x j = 1)) := by sorry

end TwoStageMatch
