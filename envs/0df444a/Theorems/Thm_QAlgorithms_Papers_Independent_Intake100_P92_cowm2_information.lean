-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_cowm2_information
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.cowm2_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:35:45.516056+00:00
-- url     : https://prove2.me/theorems/c5d05842-4b9d-4174-80fb-d52f282e6168
-- title:
--   COWm2 1PA product-state information and squared overlap
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   For $\mu\ge0$, unit vectors $v_0,v_\mu,p_0,p_\mu$ obey $\langle v_0,v_\mu\rangle=e^{-\mu/2}$ and $|\langle v_\mu,p_\mu\rangle|^2=V$. Replace the unconstrained $p_0$ by a flag orthogonal to the other vectors. The two correct key states are $p_\mu\otimes v_0$ and $v_0\otimes p_\mu$; the error states are $v_\mu\otimes p_0$ and $p_0\otimes v_\mu$. Construct each Alice/Bob marginal using weights $1-Q,Q$. Then
--
--   $$\chi_{AE}=\chi_{BE}=Q+(1-Q)h\!\left(\frac{1+|\langle v_0,p_\mu\rangle|^2}{2}\right),\qquad r_0=\frac\mu2[1-h(Q)-\chi_{AE}].$$
--
--   The constructed marginals are normalized, all constraints are preserved, and the original leakages are bounded by these values. The squared overlap comes from the swapped product factors. This is a one-pulse attack result.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 7, IV C, Eqs.(28)–(33): COWm2 1PA information and rate coefficient

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

/-- PDF pp.7–8, (28)–(33): COWm2 1PA information, with the essential squared
single-pulse overlap. No optimality against arbitrary two-pulse attacks is claimed. -/
theorem cowm2_information {I : Type*} [Fintype I] [DecidableEq I]
    (A : OneData I) (mu V Q : ℝ) (hmu : 0 ≤ mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) (hQ : Q ∈ Set.Icc (0:ℝ) 1)
    (hA : CowOneValid A mu V) :
    CowOneValid (flaggedOne A) mu V ∧
    (∀ a, weightedAncillaTrace (cowA (oneToPair (flaggedOne A)) Q a) = 1 ∧
      weightedAncillaTrace (cowB (oneToPair (flaggedOne A)) Q a) = 1) ∧
    (let L := Q + (1-Q)*QAlgorithms.binEntropy2
      ((1+Complex.normSq (inner ℂ (A.v false) (A.p true)))/2)
     binaryHolevoBits (cowA (oneToPair (flaggedOne A)) Q false)
       (cowA (oneToPair (flaggedOne A)) Q true) = L ∧
     binaryHolevoBits (cowB (oneToPair (flaggedOne A)) Q false)
       (cowB (oneToPair (flaggedOne A)) Q true) = L ∧
     binaryHolevoBits (cowA (oneToPair A) Q false) (cowA (oneToPair A) Q true) ≤ L ∧
     binaryHolevoBits (cowB (oneToPair A) Q false) (cowB (oneToPair A) Q true) ≤ L ∧
     dw (mu/2) Q L L = mu/2*(1-QAlgorithms.binEntropy2 Q-L)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
