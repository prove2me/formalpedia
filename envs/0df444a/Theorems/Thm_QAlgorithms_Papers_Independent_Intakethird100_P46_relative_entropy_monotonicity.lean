-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P46_relative_entropy_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P46.relative_entropy_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:27:17.821324+00:00
-- url     : https://prove2.me/theorems/b164f25f-51d1-4eb0-9947-2bfb48a0a7d2
-- title:
--   Relative entropy decreases under positive trace-preserving maps
-- statement:
--   Let $H$ and $H'$ be complex separable Hilbert spaces, let $\mathcal T(H)$ denote all trace-class operators, and let $\Phi:\mathcal T(H)\to\mathcal T(H')$ be complex-linear, positive, and trace-preserving on every positive trace-class input. For arbitrary positive trace-class operators $\rho,\sigma$, with no trace normalization, support, or finite-entropy assumption,
--
--   $$D(\Phi(\rho)\Vert\Phi(\sigma))\le D(\rho\Vert\sigma).$$
--
--   Here $D$ is the literal unnormalized Umegaki relative entropy $\operatorname{tr}[\rho(\log\rho-\log\sigma)]$ in natural units, interpreted as $+\infty$ on support failure or a divergent logarithmic expectation, and $D(0\Vert\sigma)=0$. This gives data processing under positivity alone.
--
--   **Formalization Note** Arbitrary countable Hilbert bases represent the two separable spaces. The accepted corrected extended divergence is embedded in the extended reals and only the finite correction $\operatorname{tr}\sigma-\operatorname{tr}\rho$ is subtracted.
-- source:
--   Monotonicity of the Quantum Relative Entropy Under Positive Maps, arXiv:1512.06117v3, PDF p. 2, Theorem 1: monotonicity of quantum relative entropy under positive trace-preserving maps

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P46

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass TraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Bridge50.P49 (beigiSandwichedDivergence)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Müller-Hermes–Reeb, arXiv:1512.06117v3, PDF p.2, Theorem 1, (3).
Countable arbitrary Hilbert bases represent exactly the separable Hilbert-space
setting; no eigenbasis, normalization, support, or finite-entropy premise is used. -/
theorem relative_entropy_monotonicity {I J : Type*} [Countable I] [Countable J]
    (b : HilbertBasis I ℂ H) (c : HilbertBasis J ℂ K)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K))
    (hPhi : PositiveTracePreservingBetween b c Phi)
    (rho sigma : TraceClass H) (hrho : IsPositive rho.val) (hsigma : IsPositive sigma.val) :
    literalTraceClassRelativeEntropy c
        (traceClassImage Phi hPhi.1 rho) (traceClassImage Phi hPhi.1 sigma) ≤
      literalTraceClassRelativeEntropy b rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P46

end
