-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P46_relative_entropy_monotonicity_trace_nonincreasing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P46.relative_entropy_monotonicity_trace_nonincreasing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:28:43.699453+00:00
-- url     : https://prove2.me/theorems/f5d44083-697b-42c0-8d13-8a4247b254bc
-- title:
--   Relative entropy decreases when a positive trace-nonincreasing map preserves the first input trace
-- statement:
--   Let $H,H'$ be complex separable Hilbert spaces, and let $\Phi:\mathcal T(H)\to\mathcal T(H')$ be complex-linear, positive, and trace-nonincreasing on every positive trace-class input. Let $\rho,\sigma\ge0$ be trace-class operators satisfying only the additional local equality $\operatorname{tr}\Phi(\rho)=\operatorname{tr}\rho$. Then
--
--   $$D(\Phi(\rho)\Vert\Phi(\sigma))\le D(\rho\Vert\sigma).$$
--
--   The divergence $D$ is the unnormalized natural-log Umegaki relative entropy, with extended values and $D(0\Vert\sigma)=0$. No trace condition is imposed on $\sigma$, no global trace preservation is required, and no support or entropy-finiteness assumption is made. This identifies the input-dependent trace condition that suffices beyond trace-preserving maps.
-- source:
--   Monotonicity of the Quantum Relative Entropy Under Positive Maps, arXiv:1512.06117v3, PDF p. 3, Theorem 1′: relative-entropy monotonicity for trace-nonincreasing maps preserving tr(ρ)

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

/-- Müller-Hermes–Reeb, arXiv:1512.06117v3, PDF p.3, Theorem 1', (6).
Global trace nonincrease is supplemented by trace preservation only at rho.
Neither global trace preservation nor preservation at sigma is assumed. -/
theorem relative_entropy_monotonicity_trace_nonincreasing
    {I J : Type*} [Countable I] [Countable J]
    (b : HilbertBasis I ℂ H) (c : HilbertBasis J ℂ K)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K))
    (hPhi : PositiveTraceNonincreasingBetween b c Phi)
    (rho sigma : TraceClass H) (hrho : IsPositive rho.val) (hsigma : IsPositive sigma.val)
    (hTrace : operatorTrace c (Phi rho.val) = operatorTrace b rho.val) :
    literalTraceClassRelativeEntropy c
        (traceClassImage Phi hPhi.1 rho) (traceClassImage Phi hPhi.1 sigma) ≤
      literalTraceClassRelativeEntropy b rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P46

end
