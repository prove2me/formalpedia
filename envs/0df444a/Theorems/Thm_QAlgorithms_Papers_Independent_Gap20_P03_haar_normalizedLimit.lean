-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_haar_normalizedLimit
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.haar_normalizedLimit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:28:33.954435+00:00
-- url     : https://prove2.me/theorems/84ff4882-1f5e-4baa-aa41-c26b112b55d3
-- title:
--   Unnumbered: normalized Haar entropy tends to the maximal rate
-- statement:
--   For positive integer dimensions let $h_d=(\sum_{i=2}^d1/i)/\ln2$. Then
--   $$\lim_{d\to\infty}\frac{h_d}{\log_2d}=1.$$
--   The isolated undefined ordinary quotient at $d=1$ is irrelevant to the limit. This states convergence of the normalized entropy rate to its maximum, not convergence of the additive difference to zero.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 21, Unnumbered: normalized Haar entropy tends to the maximal rate

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Appendix B, p.21: h_d/log_2(d) tends to one. The isolated quotient at d=1
has no effect on this atTop limit; no additive convergence is asserted. -/
theorem haar_normalizedLimit :
    Tendsto (fun d : ℕ => haarBound d / Real.logb 2 d) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
