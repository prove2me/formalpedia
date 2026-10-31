-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_cow_information
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.cow_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:33:16.79667+00:00
-- url     : https://prove2.me/theorems/432cf664-2cf7-4049-9149-1a4ddc835cc7
-- title:
--   COW 2PA orthogonal error flags and conditional information
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   For $\mu\ge0$, let $v_x,p_x^{10},p_x^{01}$ denote the vacuum and photon ancillae for each occupancy pair $x$. For nonempty input pairs $x,y$, impose $\langle v_x,v_y\rangle=e^{-\mu d_H(x,y)/2}$, the decoy visibility $\operatorname{Re}\langle p_{\mu\mu}^{01},p_{\mu\mu}^{10}\rangle=V$, and all four boundary products $\operatorname{Re}(\langle v_{l\mu},p_{l\mu}^{01}\rangle\langle p_{\mu r}^{10},v_{\mu r}\rangle)=V$. Here $d_H$ counts differing occupancy slots and $l,r$ independently denote empty or nonempty pulses.
--
--   Construct the Alice and Bob conditional mixtures from the key photon vectors with weights $1-Q,Q$. Replacing the two unconstrained key error vectors by independent orthogonal flags preserves every constraint and maximizes both leakages. If $c=|\langle p_{\mu0}^{10},p_{0\mu}^{01}\rangle|$, the resulting normalized mixtures satisfy
--
--   $$\chi_{AE}=\chi_{BE}=Q+(1-Q)h((1+c)/2),\qquad r_0=\frac\mu2[1-h(Q)-\chi_{AE}].$$
--
--   Each original leakage is bounded above by this constructed leakage, and the error flags are perfectly distinguishable. This separates a maximizing construction from premises on arbitrary attacks.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 5, IV A, Eqs.(9)–(16): original COW 2PA information and rate coefficient

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P92

open QAlgorithms.Papers.Independent.Information100.P21 (Vec tensor)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (Fock coherentPair coherentPairCoefficients passiveApply passiveCoefficients
   fockReducedFirst reducedSecond coherentCoefficient)

/-- PDF pp.5–6, (9)–(16): COW orthogonal-flag maximizing construction,
conditional information and signed first-order rate. The error branch is perfectly
distinguishable; the construction leaves all monitored Gram constraints intact. -/
theorem cow_information {I : Type*} [Fintype I] [DecidableEq I]
    (A : PairData I) (mu V Q : ℝ) (hmu : 0 ≤ mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) (hQ : Q ∈ Set.Icc (0:ℝ) 1)
    (hA : CowValid A mu V false) :
    CowValid (flaggedPair A) mu V false ∧
    (∀ a, weightedAncillaTrace (cowA (flaggedPair A) Q a) = 1 ∧
      weightedAncillaTrace (cowB (flaggedPair A) Q a) = 1) ∧
    inner ℂ ((flaggedPair A).p (true,false) true)
      ((flaggedPair A).p (false,true) false) = 0 ∧
    binaryHolevoBits (cowA (flaggedPair A) Q false) (cowA (flaggedPair A) Q true) = cowLeak A Q ∧
    binaryHolevoBits (cowB (flaggedPair A) Q false) (cowB (flaggedPair A) Q true) = cowLeak A Q ∧
    binaryHolevoBits (cowA A Q false) (cowA A Q true) ≤ cowLeak A Q ∧
    binaryHolevoBits (cowB A Q false) (cowB A Q true) ≤ cowLeak A Q ∧
    cowCoefficient A mu Q = mu/2*(1-QAlgorithms.binEntropy2 Q-cowLeak A Q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
