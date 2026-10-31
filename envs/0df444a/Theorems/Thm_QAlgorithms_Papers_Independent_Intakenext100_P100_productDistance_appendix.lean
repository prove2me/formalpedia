-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_productDistance_appendix
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.productDistance_appendix
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:23:04.590975+00:00
-- url     : https://prove2.me/theorems/429ca0fc-3744-4404-824b-e287331e5926
-- title:
--   Prime-power refined trace-norm estimate
-- statement:
--   Let $d\ge2$ and let $d'$ be any prime power with $d\le d'<2d$. For every density matrix $\rho$ on $\mathbb C^d\otimes\mathbb C^d$, write $\rho_A$ and $\rho_B$ for its partial traces. Then
--   $$\|\rho-\rho_A\otimes\rho_B\|_1\le(d'+1)^2\sqrt{2\ln(2)I_c(\rho)}.$$
--   The norm is the full Schatten one-norm and no smallness condition on $I_c$ is imposed. Unlike the communication theorem, this result does not require the chosen prime power to be least.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 6, Lemma 1, Eq. (19); proof Eq. (27) on PDF p. 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6--7, Lemma 1, Eqs.(19),(27): EVERY qualifying prime power, not
only the least one. Full Schatten 1 norm; no small-correlation threshold. -/
theorem productDistance_appendix {d dp : ℕ} (hd : 2 ≤ d)
    (hprime : IsPrimePower dp) (hlower : d ≤ dp) (hupper : dp < 2*d)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    traceNorm (rho - Matrix.kronecker (traceRight rho) (traceLeft rho)) ≤
      ((dp : ℝ)+1)^2 * correlationRoot rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
