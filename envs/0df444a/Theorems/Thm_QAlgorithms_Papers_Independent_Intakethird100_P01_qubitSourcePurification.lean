-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P01_qubitSourcePurification
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P01.qubitSourcePurification
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:45:58.411484+00:00
-- url     : https://prove2.me/theorems/1f8cac2a-0833-428c-8c8a-adb27b96f086
-- title:
--   Uniform qubit preparations realized by local projective measurements of a singlet
-- statement:
--   Let $X=(\psi_x)_{x\in\{0,1\}}$ and $Z=(\phi_z)_{z\in\{0,1\}}$ be any two orthonormal bases of $\mathbb C^2$. Share the normalized singlet
--   $$
--   |\Psi^-\rangle=\frac{|01\rangle-|10\rangle}{\sqrt2}.
--   $$
--   For a desired vector $\psi=(a,b)$, use the first-qubit measurement vector $v_\psi=(\overline b,-\overline a)$. For each basis these vectors form a complete orthonormal projective measurement. Each outcome has probability $1/2$, and the conditional density operator of the second qubit is the pure density operator of the corresponding desired vector. If $M_x=|v_{\psi_x}\rangle\langle v_{\psi_x}|$ and $N_z=|v_{\phi_z}\rangle\langle v_{\phi_z}|$, then
--   $$
--   \max_{x,z}\|\sqrt{M_x}\sqrt{N_z}\|_{\mathrm{op}}^2
--   =\max_{x,z}|\langle\psi_x,\phi_z\rangle|^2.
--   $$
--   Thus the two source descriptions give the same preparation quality, defined as minus the base-two logarithm of this overlap. Equality of the emitted density operators makes the assertion independent of a global phase convention.
-- source:
--   Tight Finite-Key Analysis for Quantum Cryptography, arXiv:1103.4130v2, PDF p. 11, Supplementary Note 1, source-model reduction; also Methods, PDF p.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P01

namespace QAlgorithms.Papers.Independent.Intakethird100.P01

open scoped BigOperators ComplexConjugate ComplexOrder

-- Accepted extended entropy: the finite-real smoothing helper excludes radius >= 1.

open QAlgorithms.Papers.Independent.Information100.P67
  (IsSubnormalized purifiedDistance conditionalMaxEntropy smoothConditionalMaxEntropyExtended)

noncomputable section

/-- PDF pp.9,11: any two orthonormal pure qubit bases admit the stated singlet preparation,
with uniform outcomes and the same preparation/measurement overlap. Density equality avoids
imposing an unphysical global-phase convention on remote preparations. -/
theorem qubitSourcePurification (X Z : Bool → EuclideanSpace ℂ Bool)
    (hX : Orthonormal ℂ X) (hZ : Orthonormal ℂ Z) :
    IsState singletKet ∧ RealizesUniformQubitBasis X ∧ RealizesUniformQubitBasis Z ∧
      preparationMeasurementOverlap X Z = preparationOverlap X Z := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P01
