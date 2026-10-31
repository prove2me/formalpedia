-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_cowm2_overlap_optimum
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.cowm2_overlap_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:41:48.944021+00:00
-- url     : https://prove2.me/theorems/3e31e3f7-48e7-477a-be9a-cb6b1b86497d
-- title:
--   Attained COWm2 overlap minimum in both visibility regimes
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   For $\mu>0$, minimize $|\langle v_0,p_\mu\rangle|$ over unit vectors obeying $\langle v_0,v_\mu\rangle=e^{-\mu/2}$ and $|\langle v_\mu,p_\mu\rangle|^2=V$. The universal lower bound is attained by the constructed (D3) family:
--
--   $$m=\max\{0,e^{-\mu/2}\sqrt V-\sqrt{1-e^{-\mu}}\sqrt{1-V}\}.$$
--
--   For $e^{-\mu}>1-V$ this is the positive (D4) expression, attained with zero angles. Otherwise a zero-overlap witness exists. Its error flag is in a fresh direction, and the constructed Alice and Bob leakages equal $L=Q+(1-Q)h((1+m^2)/2)$, giving $r_0=\frac\mu2[1-h(Q)-L]$. A positive coefficient requires $e^{-\mu}>1-V$. Endpoint witnesses avoid dividing by $V$ or $1-V$. This is the one-pulse optimum and retains the squared two-pulse overlap.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 14, Appendix D, (D1)–(D4): analytic COWm2 overlap minimum in both regimes

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

/-- Appendix D pp.14–15, (D1)–(D4): the exact overlap minimum in both regimes,
attained by a normalized feasible family. The COWm2 Holevo formula uses the
square of this overlap; positivity requires exp(-mu)>1-V in this attack model. -/
theorem cowm2_overlap_optimum (mu V : ℝ) (hmu : 0 < mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) :
    CowOneValid (cowm2Optimum mu V) mu V ∧
    cowm2Minimum mu V = max 0 (Real.exp (-mu/2)*Real.sqrt V -
      Real.sqrt (1-Real.exp (-mu))*Real.sqrt (1-V)) ∧
    ‖inner ℂ ((cowm2Optimum mu V).v false) ((cowm2Optimum mu V).p true)‖ =
      cowm2Minimum mu V ∧
    (∀ (I : Type*) [Fintype I] (A : OneData I), CowOneValid A mu V →
      cowm2Minimum mu V ≤ ‖inner ℂ (A.v false) (A.p true)‖) ∧
    (∀ Q ∈ Set.Icc (0:ℝ) 1,
      let L := Q+(1-Q)*QAlgorithms.binEntropy2 ((1+(cowm2Minimum mu V)^2)/2)
      binaryHolevoBits (cowA (oneToPair (cowm2Optimum mu V)) Q false)
        (cowA (oneToPair (cowm2Optimum mu V)) Q true) = L ∧
      binaryHolevoBits (cowB (oneToPair (cowm2Optimum mu V)) Q false)
        (cowB (oneToPair (cowm2Optimum mu V)) Q true) = L ∧
      dw (mu/2) Q L L = mu/2*(1-QAlgorithms.binEntropy2 Q-L) ∧
      (0 < dw (mu/2) Q L L → 1-V < Real.exp (-mu))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
