-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_LatIs_latSet_eq
-- name    : PI.UnitaryGroupMassFormula.LSC.LatIs.latSet_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:07.381719+00:00
-- url     : https://prove2.me/theorems/d1719ee4-420d-4648-b736-e9735b50c238
-- title:
--   Lat Is: lat Set eq
-- statement:
--   The Lat Is construction uses the lat Set eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/LatticeIsometry.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/LatticeIsometry.lean#L27-L33

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

theorem PI.UnitaryGroupMassFormula.LSC.LatIs.latSet_eq (I : Formalism.MainNotions.S.AutInst) (x : I.GA) :
    Size.latSet I x = (Formalism.UG.CS.globLat (F := I.F)
      (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) I.L : Set (Fin I.n → I.E)) := by sorry
