-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_spectrum_entropic_rates
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.spectrum_entropic_rates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:31:35.263981+00:00
-- url     : https://prove2.me/theorems/68f65d98-d237-450a-8736-53e0dbfa54ed
-- title:
--   Asymptotic spectra from one-shot spectrum entropies
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. For an arbitrary sequence of finite-dimensional normalized pairs $(\rho_n,\sigma_n)$, index only positive blocklengths. All rate optimizations and limit extrema are extended real. Write $G_n(R)=\operatorname{tr}\rho_n\{\rho_n\le2^{nR}\sigma_n\}$, $\underline D^\varepsilon=\sup\{R:\limsup G_n(R)\le\varepsilon\}$, and $\overline D^\varepsilon=\sup\{R:\liminf G_n(R)<\varepsilon\}$. For $0\le\varepsilon\le1$,
--   $$\underline D^\varepsilon=\sup_{\limsup\varepsilon_n\le\varepsilon}\liminf_n\frac1nD_s^{\varepsilon_n}(\rho_n\Vert\sigma_n),$$
--   $$\overline D^\varepsilon=\sup_{\liminf\varepsilon_n<\varepsilon}\liminf_n\frac1nD_s^{\varepsilon_n}(\rho_n\Vert\sigma_n).$$
--   The error sequences range over $[0,1]$; $D_s^1=+\infty$ and empty strict classes have supremum $-\infty$. This retains the displayed normalization and the source's binary threshold convention.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 22, §VIII: asymptotic spectrum via entropic Ds

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Section VIII, PDF p.22: normalized Ds and exact limsup/non-strict and
liminf/strict constraints. Endpoint Ds^1=+infinity is not replaced by zero. Source correction. Printed: The prose below Lemma 18 p.22 writes exp(nR) and identifies the inverse as Ds; its defining displays use 2^(nR) and Ds/n.
Changed: Use binary thresholds 2^(nR), positive blocklength n=k+1, and the displayed factor 1/n.
Why: The defining displays fix the binary units and rate normalization. Both error constraints and extended endpoints are retained. -/
theorem spectrum_entropic_rates (S : PairSequence) (hS : StateSequence S)
    (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) :
    quantumSpectrumRate S e false =
      optimizedEntropySequenceRate (fun k a => spectrumEntropy a (S.rho k) (S.sigma k)) e false ∧
    quantumSpectrumRate S e true =
      optimizedEntropySequenceRate (fun k a => spectrumEntropy a (S.rho k) (S.sigma k)) e true := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
