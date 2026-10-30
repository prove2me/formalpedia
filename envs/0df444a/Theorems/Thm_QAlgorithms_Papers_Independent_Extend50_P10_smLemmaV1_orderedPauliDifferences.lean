-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_smLemmaV1_orderedPauliDifferences
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.smLemmaV1_orderedPauliDifferences
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:42:39.722057+00:00
-- url     : https://prove2.me/theorems/949493a3-b2b8-4c56-af60-7dd97be730c4
-- title:
--   Augmented quadratic Pauli labels separate ordered differences
-- statement:
--   Let $n\ge1$. For a computational basis word $x\in\{0,1\}^n$, set $\alpha_x(0)=1$ and $\alpha_x(i)=(-1)^{x_i}$ for $1\le i\le n$. Define $\alpha_x^{(2)}(k,l)=\alpha_x(k)\alpha_x(l)$ for $0\le k,l\le n$. If $u_1\ne v_1$, $u_2\ne v_2$, and $(u_1,v_1)\ne(u_2,v_2)$, then
--
--   $$
--   \alpha_{u_1}^{(2)}-\alpha_{v_1}^{(2)}\ne\alpha_{u_2}^{(2)}-\alpha_{v_2}^{(2)}.
--   $$
--
--   The identity coordinate retains all first-order labels. Endpoints may coincide across the two ordered pairs; four pairwise distinct words are not required.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 26, SM Lemma V.1: augmented quadratic Pauli labels separate ordered differences

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.26, SM Lemma V.1: augmented quadratic labels distinguish different
ordered differences. The two ordered pairs need not have four distinct ends. -/
theorem smLemmaV1_orderedPauliDifferences (n : ℕ) (_hn : 1 ≤ n)
    (u1 v1 u2 v2 : Qubits n) (h1 : u1 ≠ v1) (h2 : u2 ≠ v2)
    (hpairs : (u1, v1) ≠ (u2, v2)) :
    quadraticPauliLabel u1 - quadraticPauliLabel v1 ≠
      quadraticPauliLabel u2 - quadraticPauliLabel v2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
