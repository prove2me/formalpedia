-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P11_bell_rateRegion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P11.bell_rateRegion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:48:16.992626+00:00
-- url     : https://prove2.me/theorems/2627159d-88a6-43aa-898e-c74b3a4e9a5b
-- title:
--   Complete distributed-compression region for a Bell source
-- statement:
--   Let $p_1,p_2,p_3,p_4\ge0$ sum to one, and consider the ordered ensemble of normalized Bell vectors
--
--   $$
--   |\phi^\pm\rangle=\frac{|00\rangle\pm|11\rangle}{\sqrt2},\qquad
--   |\psi^\pm\rangle=\frac{|01\rangle\pm|10\rangle}{\sqrt2}.
--   $$
--
--   Let $H(p)=-\sum_{i=1}^4p_i\log_2p_i$, with $0\log_20=0$. For arbitrary real rates,
--
--   $$
--   (R_A,R_B)\text{ is achievable}\quad\Longleftrightarrow\quad
--   R_A\ge\frac{H(p)}2\quad\text{and}\quad R_B\ge\frac{H(p)}2.
--   $$
--
--   An achievable pair uses independent blind local CPTP encoders, one noiseless quantum link from each sender, and a joint CPTP decoder, without supplied shared entanglement or side messages. For every $\delta,\epsilon>0$, every sufficiently large positive integer blocklength $n$ admits positive compressed dimensions $d_A,d_B$ with $\log_2(d_A)/n\le R_A+\delta$, $\log_2(d_B)/n\le R_B+\delta$, and ensemble-average pure-input overlap with the reconstructed density operator at least $1-\epsilon$. Draws are independent and identically distributed; this is squared fidelity, without a purifying reference.
--
--   This identifies both individual rate thresholds, including distributions with zero entries and the deterministic case $H(p)=0$.
-- source:
--   On the distributed compression of quantum information, arXiv:quant-ph/0403042v3, PDF p. 8, Theorem IV.1: complete Bell-source rate region

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P11

open MeasureTheory Filter

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Dependency50.P19 (both)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8–10, Theorem IV.1, (14): both individual inequalities and both
achievability directions, including H=0 and vanishing probabilities. -/
theorem bell_rateRegion (p : Fin 4 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (htotal : ∑ i, p i = 1) (ra rb : ℝ) :
    FiniteAchievable p bellSourceVectors ra rb ↔ shannon p / 2 ≤ ra ∧ shannon p / 2 ≤ rb := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P11

end
