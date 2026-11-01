-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_classical_hashing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.classical_hashing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:19:04.153678+00:00
-- url     : https://prove2.me/theorems/6d4069e4-1300-43fe-b472-5d9e0ae03ff5
-- title:
--   Classical random-parity verification
-- statement:
--   Let $N>0$, let $0\le m<N$, and fix distinct strings $x,y\in\{0,1\}^N$ before the questions are selected. Choose $m$ masks independently and uniformly from the nonzero $N$-bit masks. The parity of mask $s$ on $x$ is $s\cdot x$ modulo two. Then
--
--   $$\Pr[\forall j,\ s_j\cdot x=s_j\cdot y]\le2^{-m}.$$
--
--   Nonzero masks encode the source's fair questions. The empty sequence of questions has collision probability one. No equality with $2^{-m}$ is claimed for this mask distribution.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 7, Classical random-parity verification

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF pp.7--8: collision probability is at most 2^(-m), including m=0.
No equality to 2^(-m) is asserted for nonzero masks. -/
theorem classical_hashing (N m : ℕ) (hN : 0 < N) (hm : m < N)
    (x y : Qubits N) (hxy : x ≠ y) :
    hashingCollisionProbability m x y ≤ (2 : ℝ)⁻¹ ^ m := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
