-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_averageChannelTypical
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.averageChannelTypical
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:37:08.463763+00:00
-- url     : https://prove2.me/theorems/f3c43450-dd88-4b60-b8cf-696a2aaf1f76
-- title:
--   Lemma II.11: For delta>0 and x^n of type P, Tr(W_xn PiV,PW,delta sqrt(a))≥1−ad/delta².
-- statement:
--   Let finite input and output sizes be $a,d>0$, let $n>0$, and choose fine spectral resolutions. The input word $x^n$ has its actual empirical law $P$; $W_{x^n}=\bigotimes_iW_{x_i}$. In conditional variance bounds, $\delta>0$, $h=H(W\mid P)$ and $c=K_Vd\sqrt a\,\delta\sqrt n$, where $K_V=2\log_2(e)/e$. A shadow $B$ is an effect with state mass at least $\eta$. Exact-type statements use a simultaneous fine basis of the commuting states $\nu,\rho$, and require the indicated projector to be nonzero. Entropy-threshold projectors use finite sums of realizable count types, with arbitrary real threshold $L$; empty infima are $+\infty$ and exponential tails at infinity are zero.
--
--   $$
--   \operatorname{Tr}\bigl(W_{x^n}\Pi_{V,PW,\delta\sqrt a}^n\bigr)\ge1-ad/\delta^2.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 29, Lemma II.11

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

/-- Lemma II.11, PDF pp.29-30. No commutativity is assumed among the channel states;
only the average state's own fine spectral resolution is chosen. -/
theorem averageChannelTypical {a d n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (W : Fin a → Matrix (Fin d) (Fin d) ℂ) (hW : ∀ x, IsDensityMatrix (W x))
    (w : Fin n → Fin a) (average : FineResolution d)
    (haverage : average.state = ∑ x, (empiricalWeight w x : ℂ) • W x)
    (delta : ℝ) (hdelta : 0 < delta) :
    effectProb (wordTensor (fun k => W (w k))) (varianceProjector average n (delta * Real.sqrt a)) ≥
      1 - (a : ℝ) * d / delta^2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
