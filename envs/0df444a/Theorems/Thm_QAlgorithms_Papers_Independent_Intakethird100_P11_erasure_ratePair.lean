-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P11_erasure_ratePair
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P11.erasure_ratePair
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:49:29.964326+00:00
-- url     : https://prove2.me/theorems/373d3157-daa7-4f82-a2ff-e7ebdb9ea59a
-- title:
--   The uniform four-qubit erasure-code source admits (2,1)
-- statement:
--   Let $\mathcal C\subset(\mathbb C^2)^{\otimes4}$ be the span of the following orthonormal vectors:
--
--   $$
--   \frac{|0000\rangle+|1111\rangle}{\sqrt2},\quad
--   \frac{|0011\rangle+|1100\rangle}{\sqrt2},\quad
--   \frac{|0101\rangle+|1010\rangle}{\sqrt2},\quad
--   \frac{|1001\rangle+|0110\rangle}{\sqrt2}.
--   $$
--
--   The source draws a Haar-uniform unit vector from the whole four-dimensional subspace $\mathcal C$, gives Alice its first two qubits and Bob its last two, and repeats this independently at each position. Then
--
--   $$
--   (R_A,R_B)=(2,1)\text{ is achievable}.
--   $$
--
--   An achievable pair uses independent blind local CPTP encoders, one noiseless quantum link from each sender, and a joint CPTP decoder, without supplied shared entanglement or side messages. For every $\delta,\epsilon>0$, every sufficiently large positive integer blocklength $n$ admits positive compressed dimensions $d_A,d_B$ with $\log_2(d_A)/n\le R_A+\delta$, $\log_2(d_B)/n\le R_B+\delta$, and ensemble-average pure-input overlap with the reconstructed density operator at least $1-\epsilon$. Draws are independent and identically distributed; this is squared fidelity, without a purifying reference.
--
--   Uniformity includes all superpositions in $\mathcal C$, and is realized by the first column of normalized Haar $U(4)$ followed by the displayed code-space isometry. This gives an achievable point; optimality is left open.
-- source:
--   On the distributed compression of quantum information, arXiv:quant-ph/0403042v3, PDF p. 5, Section II: erasure-code example admits (2,1)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P11

open MeasureTheory Filter

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Dependency50.P19 (both)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Erasure codes example: the full continuous uniform source admits (2,1).
No claim of optimality or restriction to a finite codeword ensemble is made. -/
theorem erasure_ratePair : DistributedAchievable (fun c => erasureFidelity c) 2 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P11

end
