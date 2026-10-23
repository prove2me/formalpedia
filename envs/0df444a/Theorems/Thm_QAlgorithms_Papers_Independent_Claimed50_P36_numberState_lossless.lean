-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P36_numberState_lossless
-- name    : QAlgorithms.Papers.Independent.Claimed50.P36.numberState_lossless
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:32:05.206684+00:00
-- url     : https://prove2.me/theorems/8a14e1a3-4e96-40f9-b14e-96f9aeb64382
-- title:
--   Lossless number-state entropy maximum and capacity
-- statement:
--   Let $m\ge0$ be the transmitted mean photon budget of a noiseless one-mode number-state channel. Letters are the orthogonal number states $|n\rangle$ for every $n\in\mathbb N$, with product codewords and arbitrary collective decoding. For any probability law $p$ with $\sum_n n p_n\le m$, let $H(p)=-\sum_n p_n\log p_n$, in nats, with $0\log0=0$. Then
--
--   $$
--   p_m(n)=\frac1{1+m}\left(\frac m{1+m}\right)^n,\qquad \sum_n n p_m(n)=m,\qquad \max_{p:\,\sum_n n p_n\le m}H(p)=H(p_m)=C=g(m),
--   $$
--
--   where $g(m)=(m+1)\log(m+1)-m\log m$. All entropies in this maximization are finite. For $m>0$, $g(m)=\log(1+m)+m\log(1+1/m)$; at $m=0$, the optimizer is vacuum and the capacity is zero.
--
--   The result identifies the optimal number-state law and its operational classical information rate.
-- source:
--   Information capacity formula of quantum optical channels, arXiv:quant-ph/0105042v1, PDF p. 15, Eqs.(58)-(59)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P36

open Filter

open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

/-- PDF pp.14-15, Eqs.(58)-(59): the thermal number law attains the entropy
maximum and the noiseless number-state capacity, including the vacuum endpoint.
The reciprocal expression in (59) is asserted only for m>0. -/
theorem numberState_lossless (m : ℝ) (hm : 0 ≤ m) :
    NumberLaw m (thermalLaw m) ∧
    HasSum (fun n : ℕ => (n : ℝ) * thermalLaw m n) m ∧
    numberEntropy (thermalLaw m) ≠ ⊤ ∧
    (numberEntropy (thermalLaw m)).toReal = (Real.log 2 * bosonicEntropy m) ∧
    (∀ p : ℕ → ℝ, NumberLaw m p →
      numberEntropy p ≠ ⊤ ∧ (numberEntropy p).toReal ≤ (Real.log 2 * bosonicEntropy m)) ∧
    BddAbove (numberRates 1 m) ∧ numberCapacity 1 m = (Real.log 2 * bosonicEntropy m) ∧
    (0 < m → (Real.log 2 * bosonicEntropy m) = Real.log (1 + m) + m * Real.log (1 + 1 / m)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P36

end
