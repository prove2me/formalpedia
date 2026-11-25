-- Prove2me | Theorems.Thm_PI_WGL_pol_mem_dualWeyl
-- name    : PI.WGL.pol_mem_dualWeyl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:33.606381+00:00
-- url     : https://prove2.me/theorems/58a0d18b-8e74-482d-ae50-370242ca3579
-- title:
--   WGL: pol mem dual Weyl
-- statement:
--   The WGL construction uses the pol mem dual Weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliOps.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliOps.lean#L120-L122

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGL.pol_mem_dualWeyl (R : Type) [CommRing R] {r m : ℕ} (ν : Fin m → ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) (hf : f ∈ dualWeyl R r m ν) : pol R a b f ∈ dualWeyl R r m ν := by sorry
