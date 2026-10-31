-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_resolventProduct
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.resolventProduct
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:33:36.011903+00:00
-- url     : https://prove2.me/theorems/9ff42468-591f-4a06-843f-da419aebbc46
-- title:
--   Spectral product for the rank-one resolvent
-- statement:
--   Under the §18 hypotheses, let $\lambda_i$ be the eigenvalues of $P$ and $\mu_i$ the eigenvalues of $P-Q$, for $Q=v\varphi$, $\varphi(v)\ne0$, in dimension $d\ge1$. Both residues have simple nonresonant spectra and are in general position with $Q$, and the eigenbases are normalized by $\varphi=1$. For every $t$ with $tI-P$ invertible,
--
--   $$1+\varphi((tI-P)^{-1}v)=\frac{\prod_{i=1}^d(t-\mu_i)}{\prod_{i=1}^d(t-\lambda_i)}.$$
--
--   The numerator uses the spectrum of $P-Q$. This domain-restricted pointwise identity states the source rational formula without assigning a resolvent value at a pole.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 28, §22: Corollary

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §22 first corollary, PDF p.28. The numerator uses the P−Q spectrum.
The equality is asserted off the P spectrum, where the resolvent exists. -/
theorem resolventProduct {d : ℕ} (A : BasicODEData d) (t : ℂ)
    (ht : (t • (1 : Matrix (Fin d) (Fin d) ℂ) - A.P).det ≠ 0) :
    resolventScalar A.P A.v A.phi t =
      (∏ i, (t - A.mu i)) / (∏ i, (t - A.lambda i)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
