-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_harmonic_smooth_spread
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.harmonic_smooth_spread
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:19:09.365063+00:00
-- url     : https://prove2.me/theorems/d421912d-2fbb-434b-a053-0abea529ce4b
-- title:
--   Equation (23): harmonic-state smooth-spread lower bound
-- statement:
--   For $n\ge1$, let $H_n=\sum_{i=1}^n1/i$, $|\mu_n\rangle=H_n^{-1/2}\sum_{i=1}^ni^{-1/2}|i,i\rangle$, and $\rho_A$ its Alice reduction. With joint spectral-subset smooth spread $\Delta_\delta$ and $0\le\delta<1$,
--
--   $$\Delta_\delta(\rho_A)\ge(1-2\delta)\log_2 n-4-\log_2\log_2(n+1).$$
--
--   The explicit constant is retained, and $\log_2(n+1)\ge1$ makes the iterated logarithm well-defined. The source's preceding harmonic-number estimate is not assumed.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 8, Equation (23): harmonic-state smooth-spread lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF p.8, (23): the explicit harmonic-state bound, including its constant -4.
The preceding printed harmonic-number estimate has a base-convention error;
it is not used as a hypothesis or asserted here. -/
theorem harmonic_smooth_spread (n : ℕ) (hn : 0 < n) (delta : ℝ)
    (hzero : 0 ≤ delta) (hone : delta < 1) :
    smoothSpread (aliceDensity (harmonicState n)) delta ≥
      (1 - 2 * delta) * logTwo n - 4 - logTwo (logTwo (n + 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
