-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P05_iid_pinched_lower_tail
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P05.iid_pinched_lower_tail
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:57:22.044331+00:00
-- url     : https://prove2.me/theorems/ea0e7b09-13c9-4d3d-a982-3842ceab74a1
-- title:
--   Iid pinched information-spectrum lower tail
-- statement:
--   Let $x\mapsto\rho_x$ be a channel from a finite alphabet $\mathcal X$ to density operators on a finite-dimensional complex Hilbert space, and let $p$ be any input probability law. Write $\sigma=\sum_xp(x)\rho_x$, $I(p)=H(\sigma)-\sum_xp(x)H(\rho_x)$ in nats, $p^n(x^n)=\prod_{t=1}^np(x_t)$, and $\rho_{x^n}=\bigotimes_{t=1}^n\rho_{x_t}$. Let $\bar\rho_{x^n}=\mathcal E_{\sigma^{\otimes n}}(\rho_{x^n})$, where pinching preserves the full eigenspaces corresponding to distinct eigenvalues. For every real $a<I(p)$,
--
--   $$\lim_{n\to\infty}\sum_{x^n\in\mathcal X^n}p^n(x^n)\operatorname{Tr}\!\left[\bar\rho_{x^n}\{\bar\rho_{x^n}-e^{na}\sigma^{\otimes n}\le0\}\right]=0.$$
--
--   The braces denote the nonpositive spectral projector, including zero eigenvalues. Both occurrences of the output state inside the trace expression are pinched. Singular output states and zero input weights are allowed. This lower-tail limit links iid information to coding.
-- source:
--   A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory, arXiv:quant-ph/0208139v1, PDF p. 4, Lemma 1, (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P05

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr pinch typeI accept)

open QAlgorithms.Papers.Independent.Claimed50.P45 (pinchedTest)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Dependency50.P35 (directSum)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X I : Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

/-- PDF p.4, Lemma 1, (16): the iid pinched lower tail, including spectral ties,
tends to zero for every real a < I(p). Singular states and zero input weights
are permitted. The quantity is constructed from W and p, not a free sequence. -/
theorem iid_pinched_lower_tail (W : DensityOutputChannel X I) (p : Distribution X)
    (a : ℝ) (ha : a < channelInformationNats W p) :
    Tendsto (fun k : ℕ => pinchedLowerTail W p (k + 1) a) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P05

end
