-- Prove2me | Theorems.Thm_ScholtesStab_corollary_1
-- name    : ScholtesStab.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:04.350868+00:00
-- url     : https://prove2.me/theorems/a38adbfc-4ba1-409d-96f6-5e59315c87f8
-- title:
--   Corollary 1: active index sets of $\mathcal S$ near a C-stationary limit
-- statement:
--   Under the assumptions of Proposition 1, let $(\bar\sigma,\bar\varrho)$ be multipliers of $\bar x$ (any tuple satisfying (5) at $\bar x$; by MPCC-LICQ they are the multipliers of Proposition 1). Then for all sufficiently large $k$:
--
--   1. $a^{-}_{01}(\bar x)\subseteq\mathcal H(x^k)$ and $a^{+}_{01}(\bar x)\subseteq\mathcal N_1(x^k)$;
--   2. $a^{-}_{10}(\bar x)\subseteq\mathcal H(x^k)$ and $a^{+}_{10}(\bar x)\subseteq\mathcal N_2(x^k)$;
--   3. $a^{-}_{00}(\bar x)\subseteq\mathcal H(x^k)$ and $a^{+}_{00}(\bar x)\subseteq\mathcal N_1(x^k)\cap\mathcal N_2(x^k)$,
--
--   where $\mathcal H$ is taken with parameter $t_k$.
--
--   The signs of the limiting multipliers thus determine which constraints of the regularization are eventually active.
--
--   Differences from the source:
--   - encoding: ℝⁿ, indices j = 1, …, κ → EuclideanSpace ℝ (Fin n), indices in Fin κ (0-based); reason: a relabelling of coordinates and indices; same instances
--   - encoding: f, F₁, F₂ twice continuously differentiable (standing assumption, p.1) → ContDiff ℝ 2 fields of the structure MPCC; reason: the standing assumption is carried by every instance; same instances
--   - encoding: differentials DF(x), Hessians D²L(x) → fderiv ℝ F x : ℝⁿ →L[ℝ] ℝ and fderiv ℝ (fderiv ℝ L) x as a bilinear form; reason: the Fréchet derivative of a C² function is its differential and its second derivative is the Hessian; linear independence of differentials is that of gradients
--   - encoding: multipliers σ̄₁,ⱼ (j ∈ a₀₁), σ̄₂,ⱼ (j ∈ a₁₀), ϱ̄₁,ⱼ, ϱ̄₂,ⱼ (j ∈ a₀₀) → total functions Fin κ → ℝ whose values outside these index sets are never used; reason: every formula and count ranges over the paper's index sets only; same instances
--   - encoding: a sequence xᵗ converging to x̄ for t → 0 ("for all sufficiently small t", "for infinitely many t") → t : ℕ → ℝ with t k > 0 and t k → 0, x k → x̄; ∀ᶠ k in atTop and ∃ᶠ k in atTop; reason: the standard sequential reading of the paper's sequence; t k > 0 because S is defined for t > 0
--   - reading: the active index subsets of the multipliers (σ̄, ϱ̄) of x̄ (those of Proposition 1) → the sign-split sets of any multiplier tuple satisfying (5) at x̄; reason: under MPCC-LICQ every such tuple agrees with the multipliers of Proposition 1 on all index sets, so the sign-split sets are the same
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.8, Corollary 1

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_MPCCLICQ
import Definitions.Def_ScholtesStab_MPCC_IsCStationary
import Definitions.Def_ScholtesStab_MPCC_a01neg
import Definitions.Def_ScholtesStab_MPCC_H
import Definitions.Def_ScholtesStab_MPCC_IsKKT

namespace ScholtesStab

open MPCC Filter Topology

/-- **Corollary 1 (Active index sets).** Lämmel–Shikhman, arXiv:2501.07383v2, p.8: "Under the
assumptions of Proposition 1, we have for the active index subsets of the multipliers (σ̄, ϱ̄)
of x̄ ∈ M for all sufficiently small t:
a) a⁻₀₁(x̄) ⊂ ℋ(xᵗ) and a⁺₀₁(x̄) ⊂ 𝒩₁(xᵗ),
b) a⁻₁₀(x̄) ⊂ ℋ(xᵗ) and a⁺₁₀(x̄) ⊂ 𝒩₂(xᵗ),
c) a⁻₀₀(x̄) ⊂ ℋ(xᵗ) and a⁺₀₀(x̄) ⊂ 𝒩₁(xᵗ) ∩ 𝒩₂(xᵗ)."

**Formalization Note.** The assumptions of Proposition 1 are those of `proposition_1`. "The
multipliers (σ̄, ϱ̄) of x̄" are taken to be any `m` satisfying (5) at `x̄`; under MPCC-LICQ these
agree with the multipliers of Proposition 1 on all index sets (`multipliers_unique`), so the
sign-split sets are the same. "For all sufficiently small t" is `∀ᶠ k in atTop`. -/
theorem corollary_1 {n κ : ℕ} (P : MPCC n κ) (t : ℕ → ℝ) (x : ℕ → E n) (μ : ℕ → SMult κ)
    (xbar : E n) (m : MPCCMult κ) (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0))
    (hKKT : ∀ k, P.IsKKT (t k) (x k) (μ k)) (hx : Tendsto x atTop (𝓝 xbar))
    (hxbar : xbar ∈ P.M) (hLICQ : P.MPCCLICQ xbar) (hm : P.StatEq xbar m) :
    ∀ᶠ k in atTop,
      (P.a01neg xbar m ⊆ P.H (t k) (x k) ∧ P.a01pos xbar m ⊆ P.N1 (x k)) ∧
      (P.a10neg xbar m ⊆ P.H (t k) (x k) ∧ P.a10pos xbar m ⊆ P.N2 (x k)) ∧
      (P.a00neg xbar m ⊆ P.H (t k) (x k) ∧ P.a00pos xbar m ⊆ P.N1 (x k) ∩ P.N2 (x k)) := by sorry

end ScholtesStab
