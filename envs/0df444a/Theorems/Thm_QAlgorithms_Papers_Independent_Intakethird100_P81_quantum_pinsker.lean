-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_quantum_pinsker
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.quantum_pinsker
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:56:20.417866+00:00
-- url     : https://prove2.me/theorems/e77014e2-7fd9-4f36-9d66-2f76bceb64ed
-- title:
--   Quantum Pinsker inequality in bits
-- statement:
--   Let $\rho$ and $\sigma$ be normalized density matrices on the same finite-dimensional complex Hilbert space. Write $S_2(\rho\Vert\sigma)$ for Umegaki relative entropy with binary logarithms, taking value $+\infty$ when the support of $\rho$ is not contained in the support of $\sigma$. Let $\|M\|_1=\operatorname{Tr}\sqrt{M^\dagger M}$ be the full trace norm. Then
--   $$
--   S_2(\rho\Vert\sigma)\ge\frac{\|\rho-\sigma\|_1^2}{2\ln 2}.
--   $$
--
--   This bounds statistical distinguishability by relative entropy. Singular density matrices are included; no positive-definiteness assumption is imposed.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 9, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Theorem 1, PDF p.9 (proof pp.9–11): quantum Pinsker with base-two entropy,
including singular states and support violations. -/
theorem quantum_pinsker {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (hsigma : IsDensityMatrix sigma) :
    ENNReal.ofReal ((traceNorm (rho - sigma)) ^ 2 / (2 * Real.log 2)) ≤
      relativeEntropyBits rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
