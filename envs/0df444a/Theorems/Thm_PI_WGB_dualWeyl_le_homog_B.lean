-- Prove2me | Theorems.Thm_PI_WGB_dualWeyl_le_homog_B
-- name    : PI.WGB.dualWeyl_le_homog_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:19.628249+00:00
-- url     : https://prove2.me/theorems/99eabf90-5051-49b0-8557-ebeba2655104
-- title:
--   WGB: dual Weyl le homog B
-- statement:
--   The WGB construction uses the dual Weyl le homog B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFEqSumOfSubsetB.lean#L78-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFEqSumOfSubsetB.lean#L78-L92

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
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
open Formalism.BasicNotions MvPolynomial

theorem PI.WGB.dualWeyl_le_homog_B (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s) := by sorry
