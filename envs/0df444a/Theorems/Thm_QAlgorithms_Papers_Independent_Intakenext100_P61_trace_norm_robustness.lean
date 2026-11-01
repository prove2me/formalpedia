-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_trace_norm_robustness
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.trace_norm_robustness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:09:50.214957+00:00
-- url     : https://prove2.me/theorems/c1906635-e589-4af0-8833-d9c4d3aab8a9
-- title:
--   Lemma 5: one-sided trace-norm robustness
-- statement:
--   Let $\rho,\sigma$ be density matrices on the same finite-dimensional system, and let $0\le\varepsilon<1$. Write $\|\cdot\|_1$ for the trace norm, $\Delta(\rho)=\log_2(\operatorname{rank}\rho\,\lambda_{\max}(\rho))$, and $\Delta_e$ for the retained-eigenvalue-subset spread at mass at least $1-e$. If $\|\rho-\sigma\|_1\le\varepsilon$, then
--
--   $$\Delta(\rho)\ge\Delta_{\sqrt\varepsilon}(\sigma)+\log_2(1-\sqrt\varepsilon).$$
--
--   The endpoint $\varepsilon=0$ is included. This is a one-sided robustness estimate for the unsmoothed spread.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 4, Lemma 5: one-sided trace-norm robustness

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

section SpectralResults

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.4, Lemma 5: one-sided trace-norm robustness, including epsilon=0. -/
theorem trace_norm_robustness (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hzero : 0 ≤ epsilon) (hone : epsilon < 1)
    (hclose : traceNorm (rho - sigma) ≤ epsilon) :
    smoothSpread sigma (Real.sqrt epsilon) + logTwo (1 - Real.sqrt epsilon) ≤ spread rho := by sorry

end SpectralResults

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
