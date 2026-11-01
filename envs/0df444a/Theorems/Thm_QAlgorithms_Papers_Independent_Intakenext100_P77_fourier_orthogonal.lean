-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_fourier_orthogonal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.fourier_orthogonal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:56:45.121414+00:00
-- url     : https://prove2.me/theorems/034f8d02-1f5d-458d-93c5-e9f450ab2a9a
-- title:
--   Orthogonality of the Fourier components
-- statement:
--   Let $n\ge1$. Fix an unrestricted joint unitary attack on the $2n$ ideal two-level signals and a probe initially in a fixed pure basis state. Fix the preparation/measurement bases, a balanced test/information partition, and announced test strings $i_T,j_T$ whose probability is positive. Symmetrize the attack coherently by Eq. (2), then condition on this test outcome using its actual probability. Write $E_{i,j}$ for the resulting normalized information-register probe coefficients, with Alice's $n$ information bits uniform. These coefficients are constructed from the unitary, rather than postulated to have any Fourier or information property. The public classical channel is unjammable and Eve has access only to the quantum channel and the public transcript.
--
--   For an information input $i$, put $\phi_i=\sum_j E_{i,j}\otimes|i\oplus j\rangle$, $\eta_l=2^{-n}\sum_i(-1)^{l\cdot i}\phi_i$, and $d_l^2=\|\eta_l\|^2$. Dot products are modulo two and inner products conjugate the first argument.
--
--   For distinct $k,l\in\{0,1\}^n$,
--
--   $$\langle\eta_k\mid\eta_l\rangle=0.$$
--
--   Some components may vanish. The conclusion is pairwise orthogonality, which is the source's explicit meaning of “orthogonal basis.”
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 6, Lemma 3.1: orthogonality of Fourier components

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3.1, PDF p.6; Appendix D, pp.15--16: pairwise orthogonality, the
source's explicit 'i.e.' conclusion. Zero Fourier vectors remain permitted. -/
theorem fourier_orthogonal {n d : ℕ} (hn : 1 ≤ n)
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ) (e0 : Fin d)
    (iT jT : Qubits n)
    (hpos : 0 < testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT (fun _ => false))
    (k l : Qubits n) (hkl : k ≠ l) :
    inner ℂ (probeFourierComponent (conditionedSymmetric U e0 iT jT) k)
      (probeFourierComponent (conditionedSymmetric U e0 iT jT) l) = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
