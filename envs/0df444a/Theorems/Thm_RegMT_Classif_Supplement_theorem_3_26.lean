-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_3_26
-- name    : RegMT.Classif.Supplement.theorem_3_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:34:49.252686+00:00
-- url     : https://prove2.me/theorems/2facf820-46ce-4fcc-94dd-662c4b2fe875
-- title:
--   Theorem 3.26 — kernel regression and minimizers (corrected: min attained for ρ > 0)
-- statement:
--   Let $X=\mathbb R^n$, $Y=\mathbb R$, and let $H$ be the real RKHS of an arbitrary symmetric positive semidefinite kernel $k$. For $N\ge1$ samples write $K_{ij}=k(\hat x_i,\hat x_j)$. For a nonnegative convex Lipschitz loss and every $\rho\ge0$, the value of the lifted regression problem (30) equals
--   $$\inf_{\beta\in\mathbb R^N}\left\{\frac1N\sum_iL((K\beta)_i-\hat y_i)+\rho\operatorname{lip}(L)\sqrt{\beta^\mathsf TK\beta+1}\right\}.$$
--   For every $\rho>0$ this infimum is attained (at $\rho=0$ it need not be, so only the infimum is claimed there). For every minimizer $\beta^\star$ of this finite objective, the hypothesis $h^\star(x)=\sum_i\beta_i^\star k(x,\hat x_i)$ is optimal for (30). The statement includes this evaluation formula and the equality of its robust value with the infimum over all $H$. This preserves the regression $+1$ and allows repeated inputs and singular Gram matrices.
--
--   Differences from the source:
--   - correction: The finite programs are written with min, i.e. their minimum is claimed to be attained for every ρ ≥ 0, and every minimizer is transferred. → Equality of infima, attainment of the finite program for every ρ > 0, and the full minimizer-transfer and evaluation conclusions; at ρ = 0 only the infimum is asserted.; reason: At ρ = 0 the printed min fails, as shown by the linear kernel on ℝ, one sample x̂ = 1, ŷ = 0 (resp. ŷ = +1) and the softplus loss log(1+e^z), the finite objective tends to 0 without reaching it (DISPROOF.md). For ρ > 0 the term ρ·lip(L)·‖K^{1/2}β‖ makes the program coercive in K^{1/2}β (or L is constant), so the minimum is attained; no source case is excluded.
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 16, Theorem 3.26; Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Kernels

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem theorem_3_26 {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] (R : RKHSData (Set.univ : Set V) H)
    {N : ℕ} (hN : 0 < N) (x : Fin N → (Set.univ : Set V)) (y : Fin N → ℝ)
    (L : ℝ → ℝ) (hconvex : ConvexOn ℝ Set.univ L) (hnonneg : ∀ t, 0 ≤ L t)
    (hlip : ∃ K, LipschitzWith K L) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (⨅ h : H, liftedReg (fun i => R.feature (x i)) y Set.univ (fun s t => L (s - t)) ρ h) =
      (⨅ β : Fin N → ℝ, kernelRegObjective (gram R x) y L ρ β) ∧
    (0 < ρ → ∃ β : Fin N → ℝ,
      kernelRegObjective (gram R x) y L ρ β = (⨅ b : Fin N → ℝ, kernelRegObjective (gram R x) y L ρ b)) ∧
    (∀ β : Fin N → ℝ,
      kernelRegObjective (gram R x) y L ρ β = (⨅ b : Fin N → ℝ, kernelRegObjective (gram R x) y L ρ b) →
      liftedReg (fun i => R.feature (x i)) y Set.univ (fun s t => L (s - t)) ρ (kernelHyp R x β) =
        (⨅ h : H, liftedReg (fun i => R.feature (x i)) y Set.univ (fun s t => L (s - t)) ρ h) ∧
      ∀ t : (Set.univ : Set V), R.eval (kernelHyp R x β) t = ∑ i, β i * R.kernel t (x i)) := by sorry

end RegMT.Classif.Supplement
