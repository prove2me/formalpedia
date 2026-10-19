-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_universal_width_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P62.universal_width_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:58:19.805127+00:00
-- url     : https://prove2.me/theorems/f22926a9-b6c5-4bbf-8347-000ace4fee0a
-- title:
--   Proposition 5.4: universal width upper bounds
-- statement:
--   Let $d=\dim H\ge1$, and let $p(r)$ count integer partitions of $r$. For every $n\ge1$,
--   $$w_n(\Phi)\le\sum_{r=1}^{d^n}p(r)\le2^{d^n}-1.$$
--   For $d>1$, there is a real sequence $e_n\to0$ such that eventually $w_n(\Phi)\le(1+e_n)\exp(\pi\sqrt{2d^n/3})/(4\sqrt3)$. For $d=1$ the width is constantly one. This preserves the sharper Hardy–Ramanujan upper bound and the double-exponential scale.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 46, Proposition 5.4: universal width upper bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.46, 47, Proposition 5.4: universal width upper bounds. -/
theorem universal_width_bound [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) :
    (∀ n, 1 ≤ n → width F n ≤ ∑ r ∈ Icc 1 (Fintype.card I ^ n), partitionCount r) ∧
    (∀ n, 1 ≤ n → (∑ r ∈ Icc 1 (Fintype.card I ^ n), partitionCount r) ≤ 2 ^ (Fintype.card I ^ n) - 1) ∧
    (Fintype.card I = 1 → ∀ n, 1 ≤ n → width F n = 1) ∧
    (1 < Fintype.card I → ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧
      ∀ᶠ n in Filter.atTop, (width F n : ℝ) ≤
        (1 + e n) / (4 * Real.sqrt 3) * Real.exp (Real.pi * Real.sqrt (2 * (Fintype.card I : ℝ) ^ n / 3))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
