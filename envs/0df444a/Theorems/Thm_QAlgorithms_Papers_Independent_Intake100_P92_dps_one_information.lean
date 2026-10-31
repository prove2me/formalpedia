-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_dps_one_information
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.dps_one_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:42:32.06433+00:00
-- url     : https://prove2.me/theorems/2ad9d888-fdb9-4d59-8750-6b49e1c87a37
-- title:
--   DPS 1PA conditional mixtures, removable phase and QBER
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   For $\mu\ge0$, let $v_\sigma,p_\sigma$ be unit vectors, $\sigma\in\{+1,-1\}$, with $\langle v_+,v_-\rangle=e^{-2\mu}$ and $\operatorname{Re}(\langle v_\sigma,p_\sigma\rangle\langle p_\omega,v_\omega\rangle)=V$ for every sign pair. A common unit phase $z$ exists such that $\langle v_\sigma,p_\sigma\rangle=\sqrt Vz$, including $V=0$. Define $\psi_{\sigma\omega b}=\sigma(p_\sigma\otimes v_\omega)+(-1)^b\omega(v_\sigma\otimes p_\omega)$ and
--
--   $$\rho^{a,b}=\frac18\sum_\sigma P_{\psi_{\sigma,(-1)^a\sigma,b}},\qquad \operatorname{Tr}\rho^{a,b}=\begin{cases}(1+V)/2,&a=b,\\(1-V)/2,&a\ne b.\end{cases}$$
--
--   Alice’s marginal sums over $b$, Bob’s over $a$; all are normalized. Their actual binary Holevo quantities enter the signed expression $\mu[1-h((1-V)/2)-\min(\chi_{AE},\chi_{BE})]$, with $Q=(1-V)/2$. This records the source’s conditional-state calculation with the Bob dummy-index typo corrected.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 16, Appendix E.1a, (E1)–(E4): DPS 1PA conditional states and QBER

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

/-- Appendix E p.16, (E1)–(E4): common removable phase, correct subnormalized
traces, normalized Alice/Bob marginals and the resulting QBER. At V=0 no phase
is extracted by dividing an overlap by sqrt(V). The full actual conditional
ensembles, rather than their surrogate pure states, enter both Holevo quantities.

Source correction audited in round 1.
Printed: PDF p.16: rho_E^(B=b)=sum_b rho_E^(a,b), with b both the conditioning label and the summation dummy, and a unsummed.
Changed: Use rho_E^(B=b)=sum_a rho_E^(a,b). The local dps1B holds Bob b fixed and sums Alice a; all amplitudes, weights and remaining constraints are unchanged.
Why: The marginal conditioned on Bob must sum over Alice. The corresponding construction on PDF p.9 and the adjacent Alice marginal confirm the unique dummy-index repair.
-/
theorem dps_one_information {I : Type*} [Fintype I] [DecidableEq I]
    (A : OneData I) (mu V : ℝ) (hmu : 0 ≤ mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) (hA : DpsOneValid A mu V) :
    (∃ z : ℂ, ‖z‖ = 1 ∧ ∀ s,
      inner ℂ (A.v s) (A.p s) = (Real.sqrt V : ℂ)*z) ∧
    (∀ a b, weightedAncillaTrace (dps1Joint A a b) = (if a = b then (1+V)/2 else (1-V)/2)) ∧
    (∀ a, weightedAncillaTrace (dps1A A a) = 1 ∧ weightedAncillaTrace (dps1B A a) = 1) ∧
    dw mu ((1-V)/2) (binaryHolevoBits (dps1A A false) (dps1A A true))
      (binaryHolevoBits (dps1B A false) (dps1B A true)) =
      mu*(1-QAlgorithms.binEntropy2 ((1-V)/2) -
        min (binaryHolevoBits (dps1A A false) (dps1A A true))
          (binaryHolevoBits (dps1B A false) (dps1B A true))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
