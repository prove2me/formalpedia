-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_cow_positive_optimum
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.cow_positive_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:39:27.730072+00:00
-- url     : https://prove2.me/theorems/374b7090-1641-428f-bc2e-ed4439d22c35
-- title:
--   Attained positive COW 2PA overlap minimum and decoy completion
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   Let $\mu>0$, $\gamma=e^{-\mu}$, $1/2<V\le1$, and $\gamma>2\sqrt{V(1-V)}$. Over all normalized COW Gram-feasible configurations,
--
--   $$\min|\langle p_{0\mu}^{01},p_{\mu0}^{10}\rangle|=m=(2V-1)\gamma-2\sqrt{V(1-V)}\sqrt{1-\gamma^2}.$$
--
--   Both the universal lower bound and attainment are asserted. The attaining key vectors are the displayed (B4),(B5),(B8) vectors with $\lambda=1$ and all four angles zero, and (B9) constructs a normalized decoy completion satisfying every monitoring constraint. Independent orthogonal error flags then attain maximum leakage $Q+(1-Q)h((1+m)/2)$ and coefficient $\frac\mu2[1-h(Q)-Q-(1-Q)h((1+m)/2)]$. Every original attack’s Alice leakage is bounded by this attained value. This shows that the additional decoy constraints do not raise the overlap optimum.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 13, Appendix B, (B8),(B9): analytic COW 2PA optimum and feasible decoy completion

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

/-- Appendix B pp.12–13, (B8),(B9), and authors' proof sketch [25] on p.19:
the positive minimum holds over all normalized leading-order Gram-feasible
attacks and is attained with an explicit feasible decoy completion. -/
theorem cow_positive_optimum (mu V : ℝ) (hmu : 0 < mu)
    (hV : V ≤ 1) (hhalf : 1/2 < V)
    (hregime : 2*Real.sqrt (V*(1-V)) < Real.exp (-mu)) :
    CowValid (flaggedPair (cowPositive mu V)) mu V false ∧
    ‖inner ℂ ((cowPositive mu V).p (false,true) true)
      ((cowPositive mu V).p (true,false) false)‖ = cowMinimum mu V ∧
    (∀ (I : Type*) [Fintype I] (A : PairData I), CowValid A mu V false →
      cowMinimum mu V ≤ ‖inner ℂ (A.p (false,true) true) (A.p (true,false) false)‖) ∧
    (∀ Q ∈ Set.Icc (0:ℝ) 1,
      cowLeak (cowPositive mu V) Q =
        Q+(1-Q)*QAlgorithms.binEntropy2 ((1+cowMinimum mu V)/2) ∧
      cowCoefficient (cowPositive mu V) mu Q = mu/2*
        (1-QAlgorithms.binEntropy2 Q-Q-(1-Q)*QAlgorithms.binEntropy2 ((1+cowMinimum mu V)/2)) ∧
      ∀ (I : Type*) [Fintype I] [DecidableEq I] (A : PairData I), CowValid A mu V false →
        binaryHolevoBits (cowA A Q false) (cowA A Q true) ≤
          Q+(1-Q)*QAlgorithms.binEntropy2 ((1+cowMinimum mu V)/2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
