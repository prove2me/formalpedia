-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_purification_dominates
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.purification_dominates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:56:01.148407+00:00
-- url     : https://prove2.me/theorems/7f196daa-6849-440c-ab07-93ce4ec68844
-- title:
--   The error-register purification dominates the mixed probes
-- statement:
--   Let $n\ge1$. Fix an unrestricted joint unitary attack on the $2n$ ideal two-level signals and a probe initially in a fixed pure basis state. Fix the preparation/measurement bases, a balanced test/information partition, and announced test strings $i_T,j_T$ whose probability is positive. Symmetrize the attack coherently by Eq. (2), then condition on this test outcome using its actual probability. Write $E_{i,j}$ for the resulting normalized information-register probe coefficients, with Alice's $n$ information bits uniform. These coefficients are constructed from the unitary, rather than postulated to have any Fourier or information property. The public classical channel is unjammable and Eve has access only to the quantum channel and the public transcript.
--
--   For an information input $i$, put $\phi_i=\sum_j E_{i,j}\otimes|i\oplus j\rangle$, $\eta_l=2^{-n}\sum_i(-1)^{l\cdot i}\phi_i$, and $d_l^2=\|\eta_l\|^2$. Dot products are modulo two and inner products conjugate the first argument.
--
--   Writing $\rho_i=\sum_j|E_{i,j}\rangle\langle E_{i,j}|$, we have
--
--   $$\operatorname{Tr}_{\mathrm{error}}|\phi_i\rangle\langle\phi_i|=\rho_i,\qquad I_{\mathrm{acc}}(i:\rho_i)\le I_{\mathrm{acc}}(i:\phi_i).$$
--
--   The information inequality holds for any normalized prior on $i$. Here $I_{\mathrm{acc}}$ optimizes the mutual information over finite POVMs. This supplies an information upper bound by enlarging Eve's hypothetical system, without claiming a physical cloning operation.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 6, Section 3.2: error-register purification dominates Eve’s mixed states

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

/-- Section 3.2, PDF p.6: the error-labelled purification has exactly Eve's
mixed-state marginal and dominates its accessible information. Priors include
the uniform code/syndrome ensembles used later; no cloning operation is claimed. -/
theorem purification_dominates {n d : ℕ} (hn : 1 ≤ n)
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ) (e0 : Fin d)
    (iT jT : Qubits n)
    (hpos : 0 < testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT (fun _ => false)) :
    let E := conditionedSymmetric U e0 iT jT
    (∀ i, traceRight (pureDensity (errorPurification E i)) = probeDensity E i) ∧
    ∀ p : Law (Qubits n),
      ensembleAccessibleInfo p.prob (probeDensity E) id ≤
        ensembleAccessibleInfo p.prob (fun i => pureDensity (errorPurification E i)) id := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
