-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_dps_restricted_family
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.dps_restricted_family
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:43:42.13636+00:00
-- url     : https://prove2.me/theorems/acdddb49-875c-4763-8723-3eb0d320080f
-- title:
--   Restricted real six-dimensional feasible DPS 2PA family
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   For $\mu\ge0$, set $\gamma=e^{-2\mu}$ and construct the real vacuum vectors (E11) in six coordinates. Their relevant third/fourth entries are $\sqrt{(1-\gamma^2)/2}$. For each sign pair $x$ choose real unit auxiliary vectors $w_x^{01},w_x^{10}$ perpendicular to $v_x$ and to each other. Construct
--
--   $$p_x^{01}=\sqrt Vv_x-\sqrt{1-V}w_x^{01},\qquad p_x^{10}=\sqrt Vv_x-\sqrt{1-V}w_x^{10}.$$
--
--   These photon vectors are unit, real, and satisfy $\langle p_x^{01},p_x^{10}\rangle=V$ and $\langle v_x,p_x^{01}\rangle=\langle v_x,p_x^{10}\rangle=\sqrt V$. Together with the vacuum overlaps $\gamma^{d_H(x,y)}$, this yields all full DPS constraints (E9),(E10). This is an explicitly restricted feasible family for the already constructed DPS information expressions; the restrictions are not claimed without loss.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 17, Appendix E.2a, (E9)–(E14): restricted real six-dimensional DPS 2PA family

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

/-- Appendix E p.17, (E9)–(E14): a restricted real six-dimensional feasible
DPS 2PA family. These auxiliary choices are restrictions, not a without-loss
parametrization of all 2PA attacks. All photon-vector conditions are derived. -/
theorem dps_restricted_family (mu V : ℝ) (hmu : 0 ≤ mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) (w : PulsePair → Bool → Vec (Fin 6))
    (hw : ∀ x b, ‖w x b‖ = 1 ∧ inner ℂ (dpsRestrictedVacuum mu x) (w x b) = 0 ∧
      ∀ i, (w x b i).im = 0)
    (horth : ∀ x, inner ℂ (w x true) (w x false) = 0) :
    DpsValid (dpsRestricted mu V w) mu V ∧
    (∀ x b, ‖(dpsRestricted mu V w).p x b‖ = 1 ∧
      inner ℂ (dpsRestrictedVacuum mu x) ((dpsRestricted mu V w).p x b) =
        (Real.sqrt V : ℂ) ∧ ∀ i, ((dpsRestricted mu V w).p x b i).im = 0) ∧
    (∀ x, inner ℂ ((dpsRestricted mu V w).p x true)
      ((dpsRestricted mu V w).p x false) = (V : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
