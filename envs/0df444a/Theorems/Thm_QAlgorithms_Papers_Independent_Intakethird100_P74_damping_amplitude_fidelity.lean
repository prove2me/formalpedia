-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_damping_amplitude_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.damping_amplitude_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:13:18.305863+00:00
-- url     : https://prove2.me/theorems/f9cbf325-51f7-401e-8263-a0de375a5d12
-- title:
--   Amplitude-damping amplitude outputs and root fidelity
-- statement:
--   Let $0\le\eta\le1$ be transmissivity. The qubit amplitude-damping channel has Kraus operators $A_0=\sqrt{1-\eta}|0\rangle\langle1|$ and $A_1=|0\rangle\langle0|+\sqrt\eta|1\rangle\langle1|$. Its computational-basis amplitude outputs are
--
--   $$
--   \rho_0=|0\rangle\langle0|,\qquad
--   \rho_1=(1-\eta)|0\rangle\langle0|+\eta|1\rangle\langle1|,
--   \qquad\sqrt{F(\rho_0,\rho_1)}=\sqrt{1-\eta}.
--   $$
--
--   This identifies the amplitude contribution to the source's root-fidelity criterion. The source's word fidelity in this sentence refers to root fidelity under its squared-$F$ convention.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 10, Appendix C.C, unnumbered: amplitude-damping amplitude channel

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF p.10, Appendix C.C: both amplitude outputs and their ROOT fidelity.
The source's word "fidelity" here means root fidelity under its §I squared-F convention. -/
theorem damping_amplitude_fidelity (eta : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1) :
    dampingAmplitude eta false = pureDensity (ket false) ∧
    dampingAmplitude eta true = (1 - (eta : ℂ)) • pureDensity (ket false) +
      (eta : ℂ) • pureDensity (ket true) ∧
    rootFidelity (dampingAmplitude eta false) (dampingAmplitude eta true) =
      Real.sqrt (1 - eta) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
