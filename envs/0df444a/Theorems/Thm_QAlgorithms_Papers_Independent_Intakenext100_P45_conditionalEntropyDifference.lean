-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_conditionalEntropyDifference
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.conditionalEntropyDifference
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:17:37.381748+00:00
-- url     : https://prove2.me/theorems/e425f12f-1a51-4edd-a815-00bfb5f71d4c
-- title:
--   §5.3, difference-of-entropies identity
-- statement:
--   For densities $\rho,\sigma$ with $\psi_0=\operatorname{Tr}(\rho\operatorname{supp}\sigma)>0$, set $R=\rho/\psi_0$ and $X=R\operatorname{supp}\sigma$. The operator $X$ has trace one and is diagonalizable with nonnegative spectrum. With the spectral logarithm set to zero on its zero eigenspace,
--
--   $$S_\sigma(\rho\|\sigma)=S_{\rm gen}(X\|\sigma)-S_{\rm gen}(X\|R).$$
--
--   Both traces defining the generalized relative entropies are real. This trace extension permits non-self-adjoint $X$ and unnormalized $R$; it is not the normalized-state Umegaki function.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 26, §5.3, difference-of-entropies identity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF p.26: §5.3, difference-of-entropies identity. -/
theorem conditionalEntropyDifference (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hpsi : 0 < (rho*support sigma).trace.re) :
    let R := (((rho*support sigma).trace.re)⁻¹ : ℂ) • rho
    let X := R*support sigma
    (∃ d, DiagonalizesNonnegative X d) ∧ X.trace=1 ∧
    supportConditionalEntropy rho sigma = generalizedRelative X sigma-generalizedRelative X R ∧
    (X*(nonnegativeSpectrumLog X-cfc Real.log sigma)).trace.im=0 ∧
    (X*(nonnegativeSpectrumLog X-cfc Real.log R)).trace.im=0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
