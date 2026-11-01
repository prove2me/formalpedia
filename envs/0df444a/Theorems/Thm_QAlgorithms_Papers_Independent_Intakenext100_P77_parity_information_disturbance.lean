-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_parity_information_disturbance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.parity_information_disturbance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:58:59.438399+00:00
-- url     : https://prove2.me/theorems/02ff62c1-cccf-44c0-acf7-ec885b3c5499
-- title:
--   One-parity information versus disturbance
-- statement:
--   Let $n\ge1$. Fix an unrestricted joint unitary attack on the $2n$ ideal two-level signals and a probe initially in a fixed pure basis state. Fix the preparation/measurement bases, a balanced test/information partition, and announced test strings $i_T,j_T$ whose probability is positive. Symmetrize the attack coherently by Eq. (2), then condition on this test outcome using its actual probability. Write $E_{i,j}$ for the resulting normalized information-register probe coefficients, with Alice's $n$ information bits uniform. These coefficients are constructed from the unitary, rather than postulated to have any Fourier or information property. The public classical channel is unjammable and Eve has access only to the quantum channel and the public transcript.
--
--   Let $C\subseteq\mathbb F_2^n$ be the binary linear code and let $S=C^\perp$ be the span of all disclosed parity rows. Equivalently the parity check matrix is a basis of $S$, so is full rank. Fix an announced syndrome coset $i_0+C$ and use its uniform distribution, independently of the fixed public code choice. Let $v\notin S$ be the PA mask, put $\widehat v=\min_{w\in S}|v\oplus w|$, and let $SD_v$ be the supremum, over all finite POVMs, of mutual information in bits on the purified states $|\phi_i\rangle\langle\phi_i|$ about $v\cdot i$. Thus both parity classes are nonempty and equally likely. Disclosed other PA bits, when present, are included in $S$.
--
--   For every real $\alpha>0$, with $P^o(c)$ the conjugate-information-basis error law of this same conditioned attack,
--
--   $$SD_v\le\alpha+\frac1\alpha\sum_{2|c|\ge\widehat v}P^o(c).$$
--
--   Equality at the tail threshold is included. This expresses Eve's accessible parity information in terms of a counterfactual error probability.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 8, Section 3.5 Eq.(7): information versus disturbance

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

/-- Section 3.5, PDF p.8, Eq.(7): purified parity information versus disturbance.
The opposite-basis probability tail includes equality at half the distance. -/
theorem parity_information_disturbance {n d : ℕ} (hn : 1 ≤ n)
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ) (e0 : Fin d)
    (iT jT : Qubits n)
    (hpos : 0 < testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT (fun _ => false))
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (i0 v : Fin n → ZMod 2)
    (hv : v ∉ binDual C) (alpha : ℝ) (ha : 0 < alpha) :
    parityInformation (conditionedSymmetric U e0 iT jT) C i0 v ≤
      alpha + conjugateTail (conditionedSymmetric U e0 iT jT)
        (distanceToSpan (binDual C) v) / alpha := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
