-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_ideal_visibility_reduction
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.ideal_visibility_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:44:17.809328+00:00
-- url     : https://prove2.me/theorems/8d057ee0-64c3-47f0-98ac-120e83daf4d4
-- title:
--   Ideal-visibility leading attacks agree with asymptotic BSA information and rates
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   For $\mu\ge0$, specialize to $V=1$ and $Q=0$ (in DPS the latter follows from visibility). Unit-overlap constraints force the monitored photon vectors to equal their vacuum companions up to a removable common phase. Define
--
--   $$H_C=h((1-e^{-\mu})/2),\qquad H_D=2h((1-e^{-2\mu})/2)-h((1-e^{-4\mu})/2).$$
--
--   For COW and COWm1 2PA and COWm2 1PA, both conditional Holevo quantities are $H_C$ and the per-$t\eta$ coefficient is $\mu(1-H_C)/2$. For DPS 1PA and 2PA both Holevo quantities are $H_D$, with coefficient $\mu(1-H_D)$. The Gram constraints retain the corresponding BSA vacuum-overlap geometry; COWm2 has $|\langle v_0,p_\mu\rangle|^2=e^{-\mu}$. This is agreement within the normalized leading model, not equality between exact finite-loss and truncated optical transformations.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 9, IV E / Appendix E: ideal-visibility attacks reduce to the asymptotic BSA

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

/-- Section IV E p.9 and Appendix E pp.17–18: ideal-visibility ancilla Gram
reduction and information/rate agreement with the asymptotic BSA. This does
not equate an exact finite-t unitary with the truncated leading-order maps. -/
theorem ideal_visibility_reduction (mu : ℝ) (hmu : 0 ≤ mu) :
    (∀ (I : Type*) [Fintype I] [DecidableEq I] (A : PairData I),
      CowValid A mu 1 false →
      (∃ z : ℂ, ‖z‖ = 1 ∧
        (∀ a, A.p (keyPair a) a = z • A.v (keyPair a)) ∧
        ∀ b, A.p (true,true) b = z • A.v (true,true)) ∧
      cowLeak A 0 = cowIdealLeak mu ∧
      cowCoefficient A mu 0 = mu/2*(1-cowIdealLeak mu)) ∧
    (∀ (I : Type*) [Fintype I] [DecidableEq I] (A : PairData I),
      CowValid A mu 1 true → cowm1Info A 0 false = cowIdealLeak mu ∧
        cowm1Info A 0 true = cowIdealLeak mu ∧
        dw (mu/2) 0 (cowm1Info A 0 false) (cowm1Info A 0 true) =
          mu/2*(1-cowIdealLeak mu)) ∧
    (∀ (I : Type*) [Fintype I] [DecidableEq I] (A : OneData I),
      CowOneValid A mu 1 →
      (∃ z : ℂ, ‖z‖ = 1 ∧ A.p true = z • A.v true) ∧
      Complex.normSq (inner ℂ (A.v false) (A.p true)) = Real.exp (-mu) ∧
      binaryHolevoBits (cowA (oneToPair A) 0 false) (cowA (oneToPair A) 0 true) = cowIdealLeak mu ∧
      dw (mu/2) 0 (cowIdealLeak mu) (cowIdealLeak mu) = mu/2*(1-cowIdealLeak mu)) ∧
    (∀ (I : Type*) [Fintype I] [DecidableEq I] (A : PairData I), DpsValid A mu 1 →
      (∃ z : ℂ, ‖z‖ = 1 ∧ ∀ x b, A.p x b = z • A.v x) ∧
      dpsInfo A false = dpsIdealLeak mu ∧ dpsInfo A true = dpsIdealLeak mu ∧
      dw mu 0 (dpsInfo A false) (dpsInfo A true) = mu*(1-dpsIdealLeak mu)) ∧
    (∀ (I : Type*) [Fintype I] [DecidableEq I] (A : OneData I), DpsOneValid A mu 1 →
      (∃ z : ℂ, ‖z‖ = 1 ∧ ∀ s, A.p s = z • A.v s) ∧
      binaryHolevoBits (dps1A A false) (dps1A A true) = dpsIdealLeak mu ∧
      binaryHolevoBits (dps1B A false) (dps1B A true) = dpsIdealLeak mu ∧
      dw mu 0 (binaryHolevoBits (dps1A A false) (dps1A A true))
        (binaryHolevoBits (dps1B A false) (dps1B A true)) = mu*(1-dpsIdealLeak mu)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
