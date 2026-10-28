-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_count_bounds_and_residue_offsets
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.count_bounds_and_residue_offsets
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:30:36.6663+00:00
-- url     : https://prove2.me/theorems/7432c824-b5ee-4581-bbd6-df6d161360f4
-- title:
--   Corollary 7.11: count bounds and residue offsets
-- statement:
--   Let $M=(T\mid\varepsilon)(HT\mid SHT)^*(\varepsilon\mid H\mid SH)A$ with $A\in\mathcal S$ atomic. Let $U$ be its matrix, $t,h$ its displayed $T$- and $H$-counts, and $k$ the least natural exponent clearing $U$ into $\mathbb Z[\omega]$. Then
--
--   $$
--   2k-3\le t\le2k+1,\qquad 2k-2\le h\le2k.
--   $$
--   Moreover, for any other such form $N$, equality of their respective least-exponent residues implies equality of both offsets $2k-t$ and $2k-h$. All differences are integer differences.
--
--   The result includes $k=0$. In particular $U=T$ has $k=0,t=1$, so this is not a general $t\le2k$ theorem.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 11, Corollary 7.11: count bounds and residue offsets

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Corollary 7.11, PDF p.11. Every subtraction takes place in Z, including at
k=0. Both bounds and the dependence of BOTH offsets solely on the residue remain. -/
theorem count_bounds_and_residue_offsets (M : ModifiedForm) :
    let k := complexLde (modifiedValue M)
    let t := modifiedTCount M
    let h := modifiedHCount M
    (2 * (k : ℤ) - 3 ≤ (t : ℤ) ∧ (t : ℤ) ≤ 2 * (k : ℤ) + 1) ∧
    (2 * (k : ℤ) - 2 ≤ (h : ℤ) ∧ (h : ℤ) ≤ 2 * (k : ℤ)) ∧
    ∀ N : ModifiedForm,
      matrixResidue (modifiedValue N) (complexLde (modifiedValue N)) =
        matrixResidue (modifiedValue M) k →
      2 * (complexLde (modifiedValue N) : ℤ) - (modifiedTCount N : ℤ) =
        2 * (k : ℤ) - (t : ℤ) ∧
      2 * (complexLde (modifiedValue N) : ℤ) - (modifiedHCount N : ℤ) =
        2 * (k : ℤ) - (h : ℤ) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
