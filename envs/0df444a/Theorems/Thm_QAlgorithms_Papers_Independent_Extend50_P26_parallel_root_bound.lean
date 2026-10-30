-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P26_parallel_root_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P26.parallel_root_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:28:55.886677+00:00
-- url     : https://prove2.me/theorems/de6af4ce-7a98-40ab-9716-0b63e7ecb9b9
-- title:
--   Stronger parallel inversion root bound
-- statement:
--   Let $d\ge2$ and $k\ge0$ be integers, and let $p_P\in[0,1]$ be the constant success probability of any fixed universal parallel exact inversion protocol. The protocol has only $k$ forward calls to the same unknown $U\in SU(d)$; arbitrary fixed preprocessing, postprocessing, and memory are allowed. Its success branch must equal $p_P$ times the inverse channel on every input, including reference-entangled inputs. Then
--
--   $$p_P\le\left(1-\frac{d^2-1}{k+d^2-1}\right)^{1/(d-1)}.$$
--
--   The power is a real power with exponent $1/(d-1)$. Its denominator is positive and its base nonnegative throughout this domain. At $k=0$ the bound is zero; at $d=2$ it is $k/(k+3)$.
--
--   This is the stronger analytical bound from which the paper derives Theorem 2.
-- source:
--   Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations, arXiv:1810.06944v3, PDF p. 3, Eq.(1)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P26

noncomputable section

open QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.3, Eq.(1): the stronger root bound, with reciprocal exponent 1/(d-1). -/
theorem parallel_root_bound (d k : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp : Attainable .parallel d k p) :
    p ≤ Real.rpow (1 - ((d : ℝ)^2-1) / ((k : ℝ)+(d : ℝ)^2-1))
      (1 / ((d : ℝ)-1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P26

end
