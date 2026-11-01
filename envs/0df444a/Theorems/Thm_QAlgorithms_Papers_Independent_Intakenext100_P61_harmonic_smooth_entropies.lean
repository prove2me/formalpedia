-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_harmonic_smooth_entropies
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.harmonic_smooth_entropies
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:18:11.986061+00:00
-- url     : https://prove2.me/theorems/ab6ce422-e671-44ef-8079-21bba7985a9f
-- title:
--   Equations (21)–(22): harmonic-state smooth spectral entropies
-- statement:
--   For an integer $n\ge1$, let $H_n=\sum_{i=1}^n1/i$, $|\mu_n\rangle=H_n^{-1/2}\sum_{i=1}^ni^{-1/2}|i,i\rangle$, and $\rho_A$ its Alice reduction. For $0\le\delta<1$, the separately smoothed spectral entropies, optimized over eigenvalue subsets of retained mass at least $1-\delta$, satisfy
--
--   $$S_{0,\delta}(\rho_A)=\log_2\min\left\{1\le k\le n:\sum_{i=k+1}^n\frac1{iH_n}\le\delta\right\},$$
--   $$S_{\infty,\delta}(\rho_A)=\log_2 H_n+\log_2\max\left\{1\le k\le n:\sum_{i=1}^{k-1}\frac1{iH_n}\le\delta\right\}.$$
--
--   The minima and maxima are over finite nonempty integer sets. The inclusive threshold and the index $k-1$ are part of the formulas.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 8, Equations (21)–(22): harmonic-state smooth spectral entropies

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF pp.7--8, (21)--(22) (displayed on p.8): exact finite harmonic-state
smooth spectral entropies, including delta=0 and n=1. -/
theorem harmonic_smooth_entropies (n : ℕ) (hn : 0 < n) (delta : ℝ)
    (hzero : 0 ≤ delta) (hone : delta < 1) :
    smoothZero (aliceDensity (harmonicState n)) delta =
      logTwo (finiteMin (harmonicTailCuts n delta) fun k => (k : ℝ)) ∧
    smoothInfinity (aliceDensity (harmonicState n)) delta =
      logTwo (harmonicSum n) + logTwo (finiteMax (harmonicHeadCuts n delta) fun k => (k : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
