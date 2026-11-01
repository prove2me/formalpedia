-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_classical_encoding_complexity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.classical_encoding_complexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:01:26.238959+00:00
-- url     : https://prove2.me/theorems/2b34e1cb-5dd2-44a3-bc21-af39fe9b98bd
-- title:
--   Classical polar encoding uses O(N log N) actual XOR and swap gates
-- statement:
--   For each $N=2^n$, let $G_N=B_NF^{\otimes n}$ over $\mathbb F_2$, where $F=\left[\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right]$ and $B_N$ reverses the $n$ address bits of a wire. Form the explicit classical circuit $E_n$ by swapping each bit-reversal wire pair once and then applying the $n$ XOR butterfly layers. Count every two-wire XOR and swap as one operation. There exist absolute constants $C>0$ and $n_0\in\mathbb N$ such that the cost bound holds for every $n\ge n_0$, and correctness holds for every $n\ge0$:
--
--
--   $$|E_n|\le C\,2^n n,\qquad \forall u\in\mathbb F_2^{2^n},\quad E_n(u)=uG_{2^n}.$$
--
--   Since $n=\log_2N$, the actual list length is $O(N\log N)$. The circuit and bound are independent of the transmitted word, information set, and frozen vector. The claim concerns classical encoding; no efficient quantum decoding theorem is supplied by the paper.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 2, Unnumbered main result: O(N log N) classical polar encoding

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered main contribution, PDF pp.1–2; actual encoder (5), p.4.
The concrete XOR/swap list implements uG_N on every word. Universal constants
and the threshold precede n and the input, hence also all coset choices.
Since N=2^n, N*n is exactly N*log_2(N). No quantum decoding complexity is claimed. -/
theorem classical_encoding_complexity :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ,
      (∀ n ≥ n0, ((recursivePolarEncoder n).length : ℝ) ≤ C * (2 ^ n : ℕ) * n) ∧
      ∀ n (u : PolarWire n → Bit), runEncoder (recursivePolarEncoder n) u = polarEncode n u := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
