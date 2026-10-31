-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_dps_information
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.dps_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:36:25.893795+00:00
-- url     : https://prove2.me/theorems/d3f1798b-9cc5-4648-a769-a7cd854c447c
-- title:
--   DPS 2PA same-pair and crossing-pair conditional information
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   For $\mu\ge0$, use twelve unit ancilla vectors indexed by phase signs $\sigma,\omega\in\{+1,-1\}$. Vacuum overlaps are $e^{-2\mu d_H(x,y)}$; impose every within-pair and crossing visibility in (37)–(39). For a same-pair event, let $\psi_{\sigma\omega b}=\sigma p_{\sigma\omega}^{10}+(-1)^b\omega p_{\sigma\omega}^{01}$. For a crossing event, let $\psi=\omega(p_{\sigma\omega}^{01}\otimes v_{\sigma'\omega'})+(-1)^b\sigma'(v_{\sigma\omega}\otimes p_{\sigma'\omega'}^{10})$. Alice’s crossing bit is the relative phase of slots two and three.
--
--   Construct the source’s same-pair and crossing marginal mixtures with projector weights $1/8$ and $1/32$, respectively. Each joint conditional block has trace $(1+V)/2$ when $a=b$ and $(1-V)/2$ otherwise; all marginals have trace one. Thus $Q=(1-V)/2$. Keeping the equiprobable alignment flag gives $\chi_A=(\chi_A^{(2)}+\chi_A^{(4)})/2$ and likewise for $\chi_B$, and
--
--   $$r_0=\mu[1-h((1-V)/2)-\min(\chi_A,\chi_B)].$$
--
--   The marginal Holevo quantities are computed from these actual mixtures. No equality between Alice and Bob leakages is assumed.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 8, IV D, Eqs.(34)–(43): DPS 2PA conditional information and rate coefficient

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

/-- PDF pp.8–9, (34)–(43): the actual DPS conditional operators are normalized,
both alignments have QBER (1-V)/2, and their flagged information enters the
signed coefficient with min(chi_A,chi_B), without asserting these quantities equal. -/
theorem dps_information {I : Type*} [Fintype I] [DecidableEq I]
    (A : PairData I) (mu V : ℝ) (hmu : 0 ≤ mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) (hA : DpsValid A mu V) :
    (∀ a b, weightedAncillaTrace (dps2Joint A a b) = (if a = b then (1+V)/2 else (1-V)/2) ∧
      weightedAncillaTrace (dps4Joint A a b) = (if a = b then (1+V)/2 else (1-V)/2)) ∧
    (∀ a, weightedAncillaTrace (dps2A A a) = 1 ∧ weightedAncillaTrace (dps2B A a) = 1 ∧
      weightedAncillaTrace (dps4A A a) = 1 ∧ weightedAncillaTrace (dps4B A a) = 1) ∧
    dw mu ((1-V)/2) (dpsInfo A false) (dpsInfo A true) =
      mu*(1-QAlgorithms.binEntropy2 ((1-V)/2)-min (dpsInfo A false) (dpsInfo A true)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
