-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_3_27
-- name    : RegMT.Classif.Supplement.theorem_3_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:35:39.627108+00:00
-- url     : https://prove2.me/theorems/242f7ac3-5349-48c6-8fda-6aba0510d28c
-- title:
--   Theorem 3.27 — kernel classification and minimizers (corrected: min attained for ρ > 0)
-- statement:
--   Let $X=\mathbb R^n$, binary labels, and a real RKHS with kernel $k$. Write $K_{ij}=k(\hat x_i,\hat x_j)$ for $N\ge1$ samples. For a nonnegative convex Lipschitz loss, $\kappa>0$ and $\rho\ge0$, the value of lifted classification (30) equals
--   $$\inf_{\beta,\lambda,s}\left\{\lambda\rho+\frac1N\sum_i s_i:\ L(\hat y_i(K\beta)_i)\le s_i,\ L(-\hat y_i(K\beta)_i)-\kappa\lambda\le s_i,\ \operatorname{lip}(L)\sqrt{\beta^\mathsf TK\beta}\le\lambda\right\}.$$
--   For every $\rho>0$ the infimum is attained by a feasible triple (at $\rho=0$ it need not be). Every minimizing feasible triple yields the optimal RKHS hypothesis $h^\star(x)=\sum_i\beta_i^\star k(x,\hat x_i)$. Its evaluation formula and equality with the optimal lifted robust value are both asserted. This retains both label constraints, the exact modulus, and the classification norm without an added $+1$, even when the Gram matrix is singular.
--
--   Differences from the source:
--   - correction: The finite programs are written with min, i.e. their minimum is claimed to be attained for every ρ ≥ 0, and every minimizer is transferred. → Equality of infima, attainment of the finite program for every ρ > 0, and the full minimizer-transfer and evaluation conclusions; at ρ = 0 only the infimum is asserted.; reason: At ρ = 0 the printed min fails, as shown by the linear kernel on ℝ, one sample x̂ = 1, ŷ = 0 (resp. ŷ = +1) and the softplus loss log(1+e^z), the finite objective tends to 0 without reaching it (DISPROOF.md). For ρ > 0 the term ρ·lip(L)·‖K^{1/2}β‖ makes the program coercive in K^{1/2}β (or L is constant), so the minimum is attained; no source case is excluded.
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 16, Theorem 3.27; Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Kernels

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem theorem_3_27 {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] (R : RKHSData (Set.univ : Set V) H)
    {N : ℕ} (hN : 0 < N) (x : Fin N → (Set.univ : Set V)) (y : Fin N → Bool)
    (L : ℝ → ℝ) (hconvex : ConvexOn ℝ Set.univ L) (hnonneg : ∀ t, 0 ≤ L t)
    (hlip : ∃ K, LipschitzWith K L) (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ) :
    (⨅ h : H, liftedClass (fun i => R.feature (x i)) y (fun s t => L (DRLogReg.Reformulation.sgn t * s)) κ ρ h) =
      kernelClassValue (gram R x) y L κ ρ ∧
    (0 < ρ → ∃ q : (Fin N → ℝ) × (ℝ × (Fin N → ℝ)), kernelClassFeasible (gram R x) y L κ q ∧
      kernelClassObjective ρ q = kernelClassValue (gram R x) y L κ ρ) ∧
    (∀ q : (Fin N → ℝ) × (ℝ × (Fin N → ℝ)), kernelClassFeasible (gram R x) y L κ q →
      kernelClassObjective ρ q = kernelClassValue (gram R x) y L κ ρ →
      liftedClass (fun i => R.feature (x i)) y (fun s t => L (DRLogReg.Reformulation.sgn t * s)) κ ρ
        (kernelHyp R x q.1) =
          (⨅ h : H, liftedClass (fun i => R.feature (x i)) y (fun s t => L (DRLogReg.Reformulation.sgn t * s)) κ ρ h) ∧
      ∀ t : (Set.univ : Set V), R.eval (kernelHyp R x q.1) t = ∑ i, q.1 i * R.kernel t (x i)) := by sorry

end RegMT.Classif.Supplement
