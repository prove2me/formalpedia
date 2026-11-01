-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_conjugate_error_law
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.conjugate_error_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:57:37.033651+00:00
-- url     : https://prove2.me/theorems/92402209-948e-4b88-912a-c322fa0db130
-- title:
--   Conjugate-basis error law
-- statement:
--   Let $n\ge1$. Fix an unrestricted joint unitary attack on the $2n$ ideal two-level signals and a probe initially in a fixed pure basis state. Fix the preparation/measurement bases, a balanced test/information partition, and announced test strings $i_T,j_T$ whose probability is positive. Symmetrize the attack coherently by Eq. (2), then condition on this test outcome using its actual probability. Write $E_{i,j}$ for the resulting normalized information-register probe coefficients, with Alice's $n$ information bits uniform. These coefficients are constructed from the unitary, rather than postulated to have any Fourier or information property. The public classical channel is unjammable and Eve has access only to the quantum channel and the public transcript.
--
--   For an information input $i$, put $\phi_i=\sum_j E_{i,j}\otimes|i\oplus j\rangle$, $\eta_l=2^{-n}\sum_i(-1)^{l\cdot i}\phi_i$, and $d_l^2=\|\eta_l\|^2$. Dot products are modulo two and inner products conjugate the first argument.
--
--   Change the information input and output bases to their conjugates, leaving the attack, test bases, and transcript fixed. If $P^o(c)$ is the resulting error probability, averaged over uniform information inputs, then
--
--   $$P^o(c)=d_c^2.$$
--
--   The conjugate coefficients are computed from $E$ by $E^o_{k,l}=2^{-n}\sum_{i,j}(-1)^{i\cdot k+j\cdot l}E_{i,j}$. This connects the Fourier spectrum to the counterfactual disturbance of the same attack.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 7, Lemma 3.2: conjugate-basis error law

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

/-- Lemma 3.2, PDF p.7, Eq.(5); Appendix E, pp.16--17: the error law in the
conjugate information bases of the SAME conditional attack equals d_c squared. -/
theorem conjugate_error_law {n d : ℕ} (hn : 1 ≤ n)
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ) (e0 : Fin d)
    (iT jT : Qubits n)
    (hpos : 0 < testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT (fun _ => false))
    (c : Qubits n) :
    probeErrorProbability (conjugateProbes (conditionedSymmetric U e0 iT jT)) c =
      fourierWeight (conditionedSymmetric U e0 iT jT) c := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
