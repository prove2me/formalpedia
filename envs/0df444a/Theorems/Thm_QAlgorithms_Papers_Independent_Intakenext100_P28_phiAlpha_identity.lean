-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_phiAlpha_identity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.phiAlpha_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:42:28.318448+00:00
-- url     : https://prove2.me/theorems/f30438ab-37dd-4902-9435-fb41785ad9cd
-- title:
--   Lemma 3: For t>0 and alpha>0,alpha!=1, phi_alpha(t)=psi(t)-psi(t^(1-alpha))/(1-alpha)
-- statement:
--   For $t>0$ and $\alpha>0$, $\alpha\ne1$, define $\psi(t)=\ln t/(t-1)$ off 1 and $\psi(1)=1$. With $\phi_\alpha$ defined by (536), continuously extended by $\phi_\alpha(1)=\alpha/(\alpha-1)$,
--
--   $$\phi_\alpha(t)=\psi(t)-\frac{\psi(t^{1-\alpha})}{1-\alpha}.$$
--
--   Only the second $\psi$ term is divided by $1-\alpha$, including at $t=1$.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 76, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Lemma 3: For t>0 and alpha>0,alpha!=1, phi_alpha(t)=scalarLogSecant(t)-scalarLogSecant(t^(1-alpha))/(1-alpha). Sason--Verdu, arXiv:1508.00335v7, PDF p.76.  -/
theorem phiAlpha_identity
    (a t : ℝ) (ha : 0 < a ∧ a ≠ 1) (ht : 0 < t) :
    phiAlpha a t = scalarLogSecant t - scalarLogSecant (Real.rpow t (1 - a)) / (1 - a) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
