-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_block_sum_eb_iff
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.block_sum_eb_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:18:02.517744+00:00
-- url     : https://prove2.me/theorems/271cef0a-900a-4205-9a73-c280ed71ab76
-- title:
--   Entanglement breaking for a diagonal-block sum
-- statement:
--   Let $d_1,d_2,n\ge1$ and let $T_i:M_{d_i}(\mathbb C)\to M_n(\mathbb C)$ be quantum channels. Define $T$ on the direct-sum input space by $T(A)=T_1(A_{11})+T_2(A_{22})$, annihilating off-diagonal blocks. Then
--   $$T\text{ is entanglement breaking}\quad\Longleftrightarrow\quad T_1\text{ and }T_2\text{ are entanglement breaking}.$$
--   For a density-matrix input the diagonal blocks are positive semidefinite but may have trace less than one.
--
--   This permits entanglement-breaking analysis of the paper's block constructions.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 12, Lemma 7.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- Lemma 7.2, PDF p.12: the diagonal-block sum is EB iff both constituent channels
are EB. The diagonal blocks of a density matrix are allowed to be subnormalized. -/
theorem block_sum_eb_iff {d1 d2 n : ℕ} (h1 : 0 < d1) (h2 : 0 < d2) (hn : 0 < n)
    (T1 : Superop (Fin d1) (Fin n)) (T2 : Superop (Fin d2) (Fin n))
    (hT1 : IsChannel T1) (hT2 : IsChannel T2) :
    IsEB (diagonalBlockSum T1 T2) ↔ IsEB T1 ∧ IsEB T2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
