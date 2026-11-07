-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_syndromeSupport_primalMembrane
-- name    : QEC.Coding.PeriodicCubical4.syndromeSupport_primalMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:24:21.861997+00:00
-- url     : https://prove2.me/theorems/f5d84579-62ea-4cf3-8bba-34dcf28f2797
-- title:
--   Periodic Cubical4: syndrome Support primal Membrane
-- statement:
--   The selected syndrome support is the tagged support of the primal loop.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L122-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L122-L143

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.syndromeSupport_primalMembrane (m : PartialPrimalMembrane (L := L)) :
    (toricHamiltonian (L := L)).syndromeSupport (primalMembraneError m) =
      (hammingSupport (primalDefectLoop m)).map
        ⟨Sum.inl, Sum.inl_injective⟩ := by sorry
