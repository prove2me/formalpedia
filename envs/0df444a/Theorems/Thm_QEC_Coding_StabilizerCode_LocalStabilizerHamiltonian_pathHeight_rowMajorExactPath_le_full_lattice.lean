-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pathHeight_rowMajorExactPath_le_full_lattice
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_rowMajorExactPath_le_full_lattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:20:31.880312+00:00
-- url     : https://prove2.me/theorems/6a0f69b9-ec26-4a23-8636-11f4ee326ac5
-- title:
--   Local Stabilizer Hamiltonian: path Height row Major Exact Path le full lattice
-- statement:
--   The exact row-major path on an `L` by `L` lattice has the naive `O(L^2)` bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L1112-L1134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L1112-L1134

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_rowMajorExactPath_le_full_lattice
    {L : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (Q : Binary (StripGeometry.Site L)) :
    H.pathHeight (StripGeometry.rowMajorExactPath Q) ≤
      2 * (L * L) * H.participationBound := by sorry
