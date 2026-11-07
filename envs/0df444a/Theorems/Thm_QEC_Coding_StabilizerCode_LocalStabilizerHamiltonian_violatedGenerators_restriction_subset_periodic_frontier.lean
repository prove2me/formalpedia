-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_restriction_subset_periodic_frontier
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_restriction_subset_periodic_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:17:36.376071+00:00
-- url     : https://prove2.me/theorems/c88e1a2a-4266-494b-9d97-59289ffbb18d
-- title:
--   Local Stabilizer Hamiltonian: violated Generators restriction subset periodic frontier
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the violated Generators restriction subset periodic frontier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L767-L842
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L767-L842

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
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
variable {κ : Type*} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_restriction_subset_periodic_frontier
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L)
    (hRowLocal :
      StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    H.violatedGenerators
        (Locality.restrictBinaryTo (StripGeometry.rowMajorPrefix L n) Q) ⊆
      H.incidentGeneratorUnion
        (StripGeometry.movingFrontier
            L stripStart stripWidth (n / L) r ∪
          StripGeometry.seamFrontier
            L stripStart stripWidth r) := by sorry
