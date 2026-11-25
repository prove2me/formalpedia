-- Prove2me | Theorems.Thm_PI_WGL_rowDiv_succ
-- name    : PI.WGL.rowDiv_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:18.954427+00:00
-- url     : https://prove2.me/theorems/4e700f25-f6d5-4f3d-a235-a9365b92fbc4
-- title:
--   WGL: row Div succ
-- statement:
--   The WGL construction uses the row Div succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliOps.lean#L91-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliOps.lean#L91-L107

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

theorem PI.WGL.rowDiv_succ (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b (k + 1) f * ((k : MvPolynomial (Fin r × Fin m) R) + 1) +
      (if a = b then rowDiv R a b k f * (k : MvPolynomial (Fin r × Fin m) R) else 0) =
      rowDiv R a b k (pol R a b f) := by sorry
