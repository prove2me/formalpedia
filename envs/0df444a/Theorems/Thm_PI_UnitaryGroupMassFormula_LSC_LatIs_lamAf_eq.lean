-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_LatIs_lamAf_eq
-- name    : PI.UnitaryGroupMassFormula.LSC.LatIs.lamAf_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:15:14.61529+00:00
-- url     : https://prove2.me/theorems/1e095933-cdbf-40a4-9792-c410bc756604
-- title:
--   Lat Is: lam Af eq
-- statement:
--   The Lat Is construction uses the lam Af eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/LatticeIsometry.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/LatticeIsometry.lean#L15-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct
open PI.LatSizeCont
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC
open PI.UnitaryGroupMassFormula.LSC.LatIs

theorem PI.UnitaryGroupMassFormula.LSC.LatIs.lamAf_eq (I : Formalism.MainNotions.S.AutInst) :
    I.Lf = Formalism.UG.latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.MainNotions.S.IntAf I.F I.E) I.L := by sorry
