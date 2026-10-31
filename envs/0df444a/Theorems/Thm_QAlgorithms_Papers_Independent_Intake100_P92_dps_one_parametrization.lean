-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_dps_one_parametrization
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.dps_one_parametrization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:43:08.869228+00:00
-- url     : https://prove2.me/theorems/cfc71baa-3e5d-4d54-9fc2-89992e55b092
-- title:
--   Complete six-parameter DPS 1PA representation up to span isometry
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   Let $\mu>0$ and $\gamma=e^{-2\mu}$. Use the exact vacuum and perpendicular vectors (E5),(E6), the half-angle residual vectors (E7), and the photon vectors
--
--   $$p_\sigma=\sqrt Vv_\sigma-\sqrt{1-V}\cos\theta_\sigma e^{i\phi_\sigma}v_\sigma^\perp-\sqrt{1-V}\sin\theta_\sigma w'_\sigma.$$
--
--   For arbitrary real parameters $\theta_+,\theta_-,\theta,\phi_+,\phi_-,\phi$, every vector is normalized and satisfies (E2),(E4). Conversely every feasible normalized quadruple has, after one common photon phase gauge, exactly these four-vector Gram data for some six parameters. An isometry between the actual spans maps each of the four vectors to its canonical representative. In (E7), both coordinates of $w'_+$ have phase $e^{i\phi/2}$, both of $w'_-$ have phase $e^{-i\phi/2}$, and its fourth coordinate has a minus sign. This is a complete representation of 1PA geometry, not a numerical optimizer claim.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 17, Appendix E.1b, (E5)–(E8): complete six-parameter DPS 1PA representation

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

/-- Appendix E pp.16–17, (E5)–(E8): feasibility for every six-angle choice,
and completeness up to a common photon phase and equality of all four-vector
Gram data. mu>0 ensures the two-dimensional vacuum basis is nondegenerate. -/
theorem dps_one_parametrization (mu V : ℝ) (hmu : 0 < mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) :
    (∀ (thetaS phiS : Bool → ℝ) (theta phi : ℝ),
      DpsOneValid (dpsOneFamily mu V thetaS phiS theta phi) mu V) ∧
    (∀ (I : Type*) [Fintype I] (A : OneData I), DpsOneValid A mu V →
      ∃ (z : ℂ) (thetaS phiS : Bool → ℝ) (theta phi : ℝ), ‖z‖ = 1 ∧
        ancillaGram (oneFamilyVectors A z) =
          ancillaGram (oneFamilyVectors (dpsOneFamily mu V thetaS phiS theta phi) 1) ∧
        SameSpanGeometry (oneFamilyVectors A z)
          (oneFamilyVectors (dpsOneFamily mu V thetaS phiS theta phi) 1)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
