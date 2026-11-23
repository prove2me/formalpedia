-- Prove2me | Theorems.Thm_PI_WGB_iotaC_mul
-- name    : PI.WGB.iotaC_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:58.844073+00:00
-- url     : https://prove2.me/theorems/8c369ed4-02a3-4850-a417-ccb4ebbbc9c0
-- title:
--   WGB: iota C mul
-- statement:
--   The WGB construction uses the iota C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFRowActRight.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFRowActRight.lean#L17-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGB.iotaC_mul (R : Type) [CommRing R] (n k : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    iotaC R n k (A * B) = iotaC R n k A * iotaC R n k B := by sorry
