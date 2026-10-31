-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_productDistance_main
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.productDistance_main
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:20:04.926189+00:00
-- url     : https://prove2.me/theorems/3e3cd385-4993-4538-bc2d-e94953cfd92c
-- title:
--   Main-text trace-norm product estimate
-- statement:
--   Let $d\ge1$ and let $\rho_{AB}$ be a positive semidefinite, trace-one matrix on $\mathbb C^d\otimes\mathbb C^d$. Let $\rho_A=\operatorname{Tr}_B\rho$ and $\rho_B=\operatorname{Tr}_A\rho$. With $I_c$ measured in bits,
--   $$\|\rho_{AB}-\rho_A\otimes\rho_B\|_1\le(2d)^2\sqrt{2\ln(2)I_c(\rho)}.$$
--   The norm is the full Schatten one-norm $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$. This relates small independently measured correlation to proximity to the product of the actual marginals.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 4, Lemma 1, Eq. (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Lemma 1, Eq.(16): full Schatten 1 norm of the product defect;
there is no factor 1/2 and no smallness hypothesis. -/
theorem productDistance_main {d : ℕ} (hd : 0 < d)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    traceNorm (rho - Matrix.kronecker (traceRight rho) (traceLeft rho)) ≤
      (2 * (d : ℝ))^2 * correlationRoot rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
