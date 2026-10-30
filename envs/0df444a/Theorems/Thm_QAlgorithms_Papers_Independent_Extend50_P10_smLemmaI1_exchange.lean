-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_smLemmaI1_exchange
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.smLemmaI1_exchange
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:39:24.641546+00:00
-- url     : https://prove2.me/theorems/631c0291-50c0-42d7-b01f-429b9129d100
-- title:
--   Spin-half exchange equals an affine SWAP operator
-- statement:
--   For distinct sites $i,j$ of an $n$-qubit register, let $S_i^a=\sigma_i^a/2$ for $a=x,y,z$, and let $P_{ij}$ exchange tensor factors $i,j$. Then
--
--   $$
--   S_i^xS_j^x+S_i^yS_j^y+S_i^zS_j^z=\frac12P_{ij}-\frac14I.
--   $$
--
--   The identity acts on the full register. This identifies each spin-half Heisenberg interaction with an element of the represented permutation algebra.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 18, SM Lemma I.1: spin-half exchange identity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.18, SM Lemma I.1 (also Eq.(9), p.12): distinct spin-half sites satisfy
S_i·S_j = (1/2) SWAP_ij − (1/4) I. -/
theorem smLemmaI1_exchange {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    spinDot i j = (1 / 2 : ℂ) • tensorPermutation 2 n (Equiv.swap i j) -
      (1 / 4 : ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
