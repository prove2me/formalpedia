-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_gaussian_minimum
-- name    : QAlgorithms.Papers.Independent.Next46.P32.gaussian_minimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:34:45.546513+00:00
-- url     : https://prove2.me/theorems/8c149208-1e72-4c78-b16a-6b93ab3824fc
-- title:
--   Gaussian Strong Conjecture 2 holds unconditionally
-- statement:
--   Let $n\ge1$, $0\le\eta\le1$, $K\ge0$, and let $\rho_b$ be an arbitrary normalized full-Fock Gaussian density, with arbitrary displacement and correlations across its $n$ modes. Assume only the finite entropy equality $S(\rho_b)=ng(K)$, where $g(x)=(x+1)\ln(x+1)-x\ln x$. Independently supply vacuum to the $a$ port and retain $c=\sqrt\eta\,a+\sqrt{1-\eta}\,b$. Then
--
--   $$
--   S(\rho_c)\ge ng((1-\eta)K).
--   $$
--
--   The identical thermal product input of mean $K$ has entropy $ng(K)$ and attains equality. This states the globally quantified Gaussian Strong Conjecture 2 without a conjecture hypothesis, including $K=0$ and both transmissivity endpoints. It does not assert the unrestricted non-Gaussian capacity converse.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 11, Appendix A.2, concluding Gaussian minimum, PDF pp.9-11

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Appendix A.2, PDF pp.9-11: Gaussian Strong Conjecture 2 holds
unconditionally, using the Gaussian result cited as [23]. No conjecture is a
hypothesis. The intensity correction to p.11 is the same as in Theorem 1. -/
theorem gaussian_minimum : GaussianStrongConjecture2 := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
