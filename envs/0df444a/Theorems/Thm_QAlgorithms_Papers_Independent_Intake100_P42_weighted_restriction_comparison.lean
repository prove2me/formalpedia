-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P42_weighted_restriction_comparison
-- name    : QAlgorithms.Papers.Independent.Intake100.P42.weighted_restriction_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:25:22.274194+00:00
-- url     : https://prove2.me/theorems/c42c2a60-0710-41e9-afe3-3158eee6ddc0
-- title:
--   Weighted comparison of three induced operator restrictions
-- statement:
--   Let $\alpha$ be a uniform crossnorm family and $X,Y,V,W$ arbitrary normed spaces over the common real or complex field. For the same algebraic operator tensor $L\in\mathcal B(X,V)\otimes\mathcal B(Y,W)$ in every term, write $\rho_{p,q}(L)$ for the induced norm of its canonical action. Then
--
--   $$\left(\inf_{0\ne u\in X\otimes Y}\frac{\|u\|_\varepsilon}{\|u\|_\alpha}\right)\rho_{\varepsilon,\varepsilon}(L)\le\rho_{\alpha,\alpha}(L)\le\left(\sup_{0\ne u\in X\otimes Y}\frac{\|u\|_\pi}{\|u\|_\alpha}\right)\rho_{\pi,\pi}(L).$$
--
--   Both coefficients depend only on the domain $X\otimes Y$. Ratios, extrema, and products are interpreted in $[0,\infty]$, with the finite nonnegative operator norms embedded there. No bounded-ratio hypothesis is added. If a domain factor is zero, all operator tensors and their norms vanish; the conventions $\inf\varnothing=\infty$, $\sup\varnothing=0$, and $\infty\cdot0=0$ give the zero inequalities.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, PDF p. 7, Corollary 4.4: weighted comparison with the injective/injective and projective/projective restrictions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

/-- PDF pp.7--8, Corollary 4.4: both coefficients involve the DOMAIN X tensor Y
only. Extended coefficients may be zero or infinite. On a zero domain the
empty infimum is infinity, empty supremum is zero, and infinity times zero is zero. -/
theorem weighted_restriction_comparison (a : CrossnormFamily F) (ha : IsUniform a)
    (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W]
    (L : TensorProduct F (X →L[F] V) (Y →L[F] W)) :
    ratioInf injectiveNorm (a.norm X Y) *
        ENNReal.ofReal (restrictedOperatorNorm injectiveNorm injectiveNorm L) ≤
      ENNReal.ofReal (restrictedOperatorNorm (a.norm X Y) (a.norm V W) L) ∧
    ENNReal.ofReal (restrictedOperatorNorm (a.norm X Y) (a.norm V W) L) ≤
      ratioSup algebraicProjectiveNorm (a.norm X Y) *
        ENNReal.ofReal (restrictedOperatorNorm algebraicProjectiveNorm algebraicProjectiveNorm L) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P42

end
