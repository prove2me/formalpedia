-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_periodicHorizontalInterval_iff
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_periodicHorizontalInterval_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:15:00.137737+00:00
-- url     : https://prove2.me/theorems/29028550-923f-4442-b170-d739182a551e
-- title:
--   Strip Geometry: mem periodic Horizontal Interval iff
-- statement:
--   The Strip Geometry construction uses the mem periodic Horizontal Interval iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L441-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L441-L447

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_periodicHorizontalInterval_iff
    {L start width : Nat} (p : Site L) :
    p ∈ periodicHorizontalInterval L start width ↔
      ((start % L ≤ p.2.val ∧
          p.2.val < start % L + width) ∨
        p.2.val + L < start % L + width) := by sorry
