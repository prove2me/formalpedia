-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_thermal_entropy_mean
-- name    : QAlgorithms.Papers.Independent.Next46.P32.thermal_entropy_mean
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:35:12.706179+00:00
-- url     : https://prove2.me/theorems/29b26af2-05e3-4518-a17a-1bc5ce9659d1
-- title:
--   Uniform entropy-mean inequality for the thermal entropy
-- statement:
--   Let $n\ge1$, let $x_0,x_1,\ldots,x_n$ be nonnegative real numbers, and let $0\le\eta\le1$. Use $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. If
--
--   $$
--   \frac1n\sum_{k=1}^{n}g(x_k)=g(x_0),
--   $$
--
--   then
--
--   $$
--   \frac1n\sum_{k=1}^{n}g(\eta x_k)\ge g(\eta x_0).
--   $$
--
--   This finite uniform averaging inequality is the entropy comparison used in the broadcast converse. It retains equality at $n=1$ and at either endpoint $\eta=0,1$; it makes no claim that $g$ itself is convex.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 12, Appendix B, Eqs. (B1)-(B2)

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

/-- Appendix B, PDF p.12, (B1)-(B2): the uniform finite entropy-mean inequality.
All occupations are nonnegative and n is positive; at eta=0, eta=1 or n=1 the
corresponding formula is an equality. No convexity of g itself is claimed. -/
theorem thermal_entropy_mean (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (x0 eta : ℝ) (hx : ∀ i, 0 ≤ x i) (hx0 : 0 ≤ x0)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hmean : (∑ i, g (x i)) / (n : ℝ) = g x0) :
    g (eta * x0) ≤ (∑ i, g (eta * x i)) / (n : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
