-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_equal_block_packing
-- name    : QAlgorithms.Papers.Independent.Information100.P62.equal_block_packing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:42:47.853305+00:00
-- url     : https://prove2.me/theorems/8e7065d3-7dd9-4265-a6f6-f11c93344899
-- title:
--   Lemma 4.5: packing equal matrix blocks
-- statement:
--   Let $B=\bigoplus_jM_{n_j}(\mathbb C)$ be nonzero and let $d\ge1$. The largest number $b_d(B)$ of equal $d$-blocks that embed in $B$, allowing the value zero, is
--   $$b_d(B)=\sum_j\lfloor n_j/d\rfloor.$$
--   Equivalently, for multiplicities $N_m\ge0$, $b_d(B)=\sum_mN_m\lfloor m/d\rfloor$. This explicitly computes equal-block packing.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 33, Lemma 4.5: packing equal matrix blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.33, 34, Lemma 4.5: packing equal matrix blocks. -/
theorem equal_block_packing (B : Shape) (hB : Valid B) (d : ℕ) (hd : 0 < d) :
    packingNumber d B = (B.map (fun n => n / d)).sum ∧
    ∀ (R : ℕ) (N : Fin R → ℕ),
      B = (List.ofFn (fun m => equalBlocks (m.val + 1) (N m))).foldl (· + ·) 0 →
      packingNumber d B = ∑ m, N m * ((m.val + 1) / d) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
