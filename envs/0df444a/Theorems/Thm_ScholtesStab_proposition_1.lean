-- Prove2me | Theorems.Thm_ScholtesStab_proposition_1
-- name    : ScholtesStab.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:18.209455+00:00
-- url     : https://prove2.me/theorems/039ccc91-e792-4e3a-bf27-ada3ec811dbf
-- title:
--   Proposition 1 (Scholtes 2001): limits of KKT points are C-stationary, with multiplier limits
-- statement:
--   Let $t_k>0$, $t_k\to0$, and let $x^k\in M^{\mathcal S}$ be Karush–Kuhn–Tucker points of $\mathcal S$ with parameter $t_k$ and multipliers $(\eta^k,\nu^k)$, converging to $\bar x\in M$. Suppose MPCC-LICQ holds at $\bar x$, and let
--
--   $$
--   I_0=\{j \mid j\in\mathcal H(x^k)\text{ for infinitely many }k\}.
--   $$
--
--   Then $\bar x$ is a C-stationary point of MPCC, with unique multipliers $(\bar\sigma,\bar\varrho)$, and these satisfy:
--
--   1. for $j\in a_{01}(\bar x)$: $\bar\sigma_{1,j}=\lim_k\nu^k_{1,j}$ if $j\notin I_0$, and $\bar\sigma_{1,j}=-\lim_k\eta^k_jF_{2,j}(x^k)$ if $j\in I_0$;
--   2. for $j\in a_{10}(\bar x)$: $\bar\sigma_{2,j}=\lim_k\nu^k_{2,j}$ if $j\notin I_0$, and $\bar\sigma_{2,j}=-\lim_k\eta^k_jF_{1,j}(x^k)$ if $j\in I_0$;
--   3. for $j\in a_{00}(\bar x)$: $\bar\varrho_{1,j}=\lim_k\nu^k_{1,j}$ and $\bar\varrho_{2,j}=\lim_k\nu^k_{2,j}$ if $j\notin I_0$, and $\bar\varrho_{1,j}=-\lim_k\eta^k_jF_{2,j}(x^k)$, $\bar\varrho_{2,j}=-\lim_k\eta^k_jF_{1,j}(x^k)$ if $j\in I_0$.
--
--   In particular all the limits exist. Uniqueness means that every tuple satisfying (5) at $\bar x$ agrees with $(\bar\sigma,\bar\varrho)$ on the index sets where the multipliers live.
--
--   This connects the multipliers of the regularized problems to those of the limit point and is the basis of every index comparison in the paper.
--
--   Differences from the source:
--   - encoding: ℝⁿ, indices j = 1, …, κ → EuclideanSpace ℝ (Fin n), indices in Fin κ (0-based); reason: a relabelling of coordinates and indices; same instances
--   - encoding: f, F₁, F₂ twice continuously differentiable (standing assumption, p.1) → ContDiff ℝ 2 fields of the structure MPCC; reason: the standing assumption is carried by every instance; same instances
--   - encoding: differentials DF(x), Hessians D²L(x) → fderiv ℝ F x : ℝⁿ →L[ℝ] ℝ and fderiv ℝ (fderiv ℝ L) x as a bilinear form; reason: the Fréchet derivative of a C² function is its differential and its second derivative is the Hessian; linear independence of differentials is that of gradients
--   - encoding: multipliers σ̄₁,ⱼ (j ∈ a₀₁), σ̄₂,ⱼ (j ∈ a₁₀), ϱ̄₁,ⱼ, ϱ̄₂,ⱼ (j ∈ a₀₀) → total functions Fin κ → ℝ whose values outside these index sets are never used; reason: every formula and count ranges over the paper's index sets only; same instances
--   - encoding: a sequence xᵗ converging to x̄ for t → 0 ("for all sufficiently small t", "for infinitely many t") → t : ℕ → ℝ with t k > 0 and t k → 0, x k → x̄; ∀ᶠ k in atTop and ∃ᶠ k in atTop; reason: the standard sequential reading of the paper's sequence; t k > 0 because S is defined for t > 0
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.8, Proposition 1

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01
import Definitions.Def_ScholtesStab_MPCC_MPCCLICQ
import Definitions.Def_ScholtesStab_MPCC_IsCStationary
import Definitions.Def_ScholtesStab_MPCC_H
import Definitions.Def_ScholtesStab_MPCC_IsKKT

namespace ScholtesStab

open MPCC Filter Topology

/-- **Proposition 1 (Multipliers, Scholtes (2001)).** Lämmel–Shikhman, arXiv:2501.07383v2, p.8:
"Suppose a sequence of Karush-Kuhn-Tucker points xᵗ ∈ Mˢ of S with multipliers (ηᵗ, νᵗ)
converges to x̄ for t → 0. Let MPCC-LICQ be fulfilled at x̄ ∈ M. Then, x̄ is a C-stationary point
of MPCC with the unique multipliers (σ̄, ϱ̄) satisfying:
a) for j ∈ a₀₁(x̄), σ̄₁,ⱼ = lim_{t→0} νᵗ₁,ⱼ if j ∉ I₀, −lim_{t→0} ηᵗⱼ F₂,ⱼ(xᵗ) if j ∈ I₀,
b) for j ∈ a₁₀(x̄), σ̄₂,ⱼ = lim_{t→0} νᵗ₂,ⱼ if j ∉ I₀, −lim_{t→0} ηᵗⱼ F₁,ⱼ(xᵗ) if j ∈ I₀,
c) for j ∈ a₀₀(x̄), ϱ̄₁,ⱼ = lim_{t→0} νᵗ₁,ⱼ if j ∉ I₀, −lim_{t→0} ηᵗⱼ F₂,ⱼ(xᵗ) if j ∈ I₀,
   and ϱ̄₂,ⱼ = lim_{t→0} νᵗ₂,ⱼ if j ∉ I₀, −lim_{t→0} ηᵗⱼ F₁,ⱼ(xᵗ) if j ∈ I₀,
where I₀ = {j | j ∈ ℋ(xᵗ) for infinitely many t}."

**Formalization Note.** "A sequence xᵗ … for t → 0" is a sequence of parameters `t k > 0` with
`t k → 0` and points `x k → x̄`, each `x k` a KKT point of S with parameter `t k` and multipliers
`μ k = (ηᵗ, νᵗ)`. `j ∈ I₀` is `∃ᶠ k in atTop, j ∈ ℋ(x k)` (for `t = t k`). "C-stationary with
the unique multipliers" is: some `m` makes `x̄` C-stationary, every `m'` satisfying (5) agrees
with `m` on the relevant index sets, and the limits exist along the whole sequence and equal
the stated multipliers (the existence of the limits is part of the conclusion). -/
theorem proposition_1 {n κ : ℕ} (P : MPCC n κ) (t : ℕ → ℝ) (x : ℕ → E n) (μ : ℕ → SMult κ)
    (xbar : E n) (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0))
    (hKKT : ∀ k, P.IsKKT (t k) (x k) (μ k)) (hx : Tendsto x atTop (𝓝 xbar))
    (hxbar : xbar ∈ P.M) (hLICQ : P.MPCCLICQ xbar) :
    ∃ m : MPCCMult κ, P.IsCStationary xbar m ∧
      (∀ m' : MPCCMult κ, P.StatEq xbar m' → P.SameMult xbar m m') ∧
      (∀ j ∈ P.a01 xbar,
        ((¬ ∃ᶠ k in atTop, j ∈ P.H (t k) (x k)) →
            Tendsto (fun k => (μ k).ν₁ j) atTop (𝓝 (m.σ₁ j))) ∧
        ((∃ᶠ k in atTop, j ∈ P.H (t k) (x k)) →
            Tendsto (fun k => -((μ k).η j * P.F₂ j (x k))) atTop (𝓝 (m.σ₁ j)))) ∧
      (∀ j ∈ P.a10 xbar,
        ((¬ ∃ᶠ k in atTop, j ∈ P.H (t k) (x k)) →
            Tendsto (fun k => (μ k).ν₂ j) atTop (𝓝 (m.σ₂ j))) ∧
        ((∃ᶠ k in atTop, j ∈ P.H (t k) (x k)) →
            Tendsto (fun k => -((μ k).η j * P.F₁ j (x k))) atTop (𝓝 (m.σ₂ j)))) ∧
      (∀ j ∈ P.a00 xbar,
        ((¬ ∃ᶠ k in atTop, j ∈ P.H (t k) (x k)) →
            Tendsto (fun k => (μ k).ν₁ j) atTop (𝓝 (m.ϱ₁ j)) ∧
            Tendsto (fun k => (μ k).ν₂ j) atTop (𝓝 (m.ϱ₂ j))) ∧
        ((∃ᶠ k in atTop, j ∈ P.H (t k) (x k)) →
            Tendsto (fun k => -((μ k).η j * P.F₂ j (x k))) atTop (𝓝 (m.ϱ₁ j)) ∧
            Tendsto (fun k => -((μ k).η j * P.F₁ j (x k))) atTop (𝓝 (m.ϱ₂ j)))) := by sorry

end ScholtesStab
