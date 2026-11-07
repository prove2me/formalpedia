-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_syndromeSupport_dualMembrane
-- name    : QEC.Coding.PeriodicCubical4.syndromeSupport_dualMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:24:54.984186+00:00
-- url     : https://prove2.me/theorems/144308fa-a43e-40ff-ac29-c5e8dd924f0f
-- title:
--   Periodic Cubical4: syndrome Support dual Membrane
-- statement:
--   The selected syndrome support is the tagged support of the dual loop.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L146-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L146-L167

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.syndromeSupport_dualMembrane (m : PartialDualMembrane (L := L)) :
    (toricHamiltonian (L := L)).syndromeSupport (dualMembraneError m) =
      (hammingSupport (dualDefectLoop m)).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by sorry
