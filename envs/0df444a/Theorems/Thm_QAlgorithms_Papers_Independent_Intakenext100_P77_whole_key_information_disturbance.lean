-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_whole_key_information_disturbance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.whole_key_information_disturbance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:59:34.477904+00:00
-- url     : https://prove2.me/theorems/c7d721cc-7797-4e7e-b660-18152a098e35
-- title:
--   Whole-key information versus disturbance
-- statement:
--   Let $n\ge1$. Fix an unrestricted joint unitary attack on the $2n$ ideal two-level signals and a probe initially in a fixed pure basis state. Fix the preparation/measurement bases, a balanced test/information partition, and announced test strings $i_T,j_T$ whose probability is positive. Symmetrize the attack coherently by Eq. (2), then condition on this test outcome using its actual probability. Write $E_{i,j}$ for the resulting normalized information-register probe coefficients, with Alice's $n$ information bits uniform. These coefficients are constructed from the unitary, rather than postulated to have any Fourier or information property. The public classical channel is unjammable and Eve has access only to the quantum channel and the public transcript.
--
--   Fix a binary code $C$, a uniform announced syndrome coset $i_0+C$, and $m\ge1$ PA rows $v_1,\ldots,v_m$ that are jointly independent modulo $C^\perp$. All choices are fixed independently of the unrevealed coset element; this implies $m\le n-\dim C^\perp$. Let $A=(v_j\cdot i)_{j=1}^m$ be the final key and
--
--   $$\widehat v=\min_j\min_{w\in C^\perp+\operatorname{span}\{v_k:k\ne j\}}|v_j\oplus w|.$$
--
--   For every real $\alpha>0$, The whole-key accessible information of the purified ensemble $|\phi_i\rangle\langle\phi_i|$ satisfies
--
--   $$I_{\mathrm{acc}}(A:E)\le m\left(\alpha+\frac1\alpha\sum_{2|c|\ge\widehat v}P^o(c)\right),$$
--
--   where $P^o$ is the conjugate-information-basis error law of the same conditional attack. The minimum accounts for disclosure of every other PA bit before bounding a single bit.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 9, Eq.(8): full-key information versus disturbance

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

/-- PDF p.9, Eq.(8): purified whole-key information versus disturbance, with all other
key bits disclosed in the distance. PA independence means full rank modulo ECC;
all public choices are fixed independently of the unknown uniform coset element. -/
theorem whole_key_information_disturbance {n d m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ) (e0 : Fin d)
    (iT jT : Qubits n)
    (hpos : 0 < testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT (fun _ => false))
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (i0 : Fin n → ZMod 2)
    (V : Fin m → Fin n → ZMod 2) (hV : IndependentPA C V)
    (alpha : ℝ) (ha : 0 < alpha) :
    wholeKeyInformation (conditionedSymmetric U e0 iT jT) C i0 V ≤
      m * (alpha + conjugateTail (conditionedSymmetric U e0 iT jT)
        (keyDistance C V) / alpha) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
