-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_exactTypeProbability
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.exactTypeProbability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:38:14.230527+00:00
-- url     : https://prove2.me/theorems/4f5c0891-bf91-4664-85fd-022b3493fd13
-- title:
--   Corollary II.13: If nu commutes with rho and Pi_nu^n≠0: (n+1)^(-d)2^(−nD(nu||rho))≤Tr(rho^n Pi_nu^n)≤2^(−nD(nu||rho)).
-- statement:
--   Let finite input and output sizes be $a,d>0$, let $n>0$, and choose fine spectral resolutions. The input word $x^n$ has its actual empirical law $P$; $W_{x^n}=\bigotimes_iW_{x_i}$. In conditional variance bounds, $\delta>0$, $h=H(W\mid P)$ and $c=K_Vd\sqrt a\,\delta\sqrt n$, where $K_V=2\log_2(e)/e$. A shadow $B$ is an effect with state mass at least $\eta$. Exact-type statements use a simultaneous fine basis of the commuting states $\nu,\rho$, and require the indicated projector to be nonzero. Entropy-threshold projectors use finite sums of realizable count types, with arbitrary real threshold $L$; empty infima are $+\infty$ and exponential tails at infinity are zero.
--
--   $$
--   \Pi_\nu^n\ne0\Longrightarrow(n+1)^{-d}2^{-nD(\nu\Vert\rho)}\le\operatorname{Tr}(\rho^{\otimes n}\Pi_\nu^n)\le2^{-nD(\nu\Vert\rho)}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 31, Corollary II.13

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Corollary II.13, PDF p.31: the nonzero exact-type projector guard is explicit.
A simultaneous fine basis represents every commuting pair, including degeneracies;
unsupported nu has divergence +infinity and contributes zero. -/
theorem exactTypeProbability {d : ℕ} (rho : FineResolution d) (nu : PMF (Fin d))
    (n : ℕ) (hn : 0 < n)
    (hrealizable : varianceProjector (changeSpectrum rho nu) n 0 ≠ 0) :
    let Pi := varianceProjector (changeSpectrum rho nu) n 0
    let tail := divergenceTail n (relativeBits (changeSpectrum rho nu).state rho.state)
    (n + 1 : ℝ)^(-(d : ℤ)) * tail ≤ effectProb (copies n rho.state) Pi ∧
    effectProb (copies n rho.state) Pi ≤ tail := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
