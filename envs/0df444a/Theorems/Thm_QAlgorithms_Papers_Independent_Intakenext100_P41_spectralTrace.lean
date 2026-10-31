-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_spectralTrace
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.spectralTrace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:34:05.674076+00:00
-- url     : https://prove2.me/theorems/e920604f-dacc-46aa-a626-8218f342ea3b
-- title:
--   Difference of spectral traces
-- statement:
--   Let $P,Q=v\varphi$ satisfy the §18 simple-spectrum, nonresonance, general-position and normalized-eigenbasis hypotheses in dimension $d\ge1$, with $\delta=\varphi(v)\ne0$. If $\lambda_i$ are the eigenvalues of $P$ and $\mu_i$ those of $P-Q$, then
--
--   $$\sum_{i=1}^d\lambda_i-\sum_{i=1}^d\mu_i=\delta=\operatorname{Tr}Q.$$
--
--   The complex eigenvalues are unordered. The identity identifies the rank-one parameter with the difference of the spectral sums.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 28, §22: Corollary

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §22 second corollary, PDF p.28: complex eigenvalues are unordered;
δ=φ(v)=Tr(Q), with Q=vφ. -/
theorem spectralTrace {d : ℕ} (A : BasicODEData d) :
    (∑ i, A.lambda i) - (∑ i, A.mu i) = A.phi A.v ∧
      A.phi A.v = Matrix.trace (linearRankOneMatrix A.v A.phi) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
