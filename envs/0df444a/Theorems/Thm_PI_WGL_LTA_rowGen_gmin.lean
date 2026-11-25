-- Prove2me | Theorems.Thm_PI_WGL_LTA_rowGen_gmin
-- name    : PI.WGL.LTA.rowGen_gmin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:28.179822+00:00
-- url     : https://prove2.me/theorems/84a782f0-f739-4b59-a141-46d21072aa94
-- title:
--   LTA: row Gen gmin
-- statement:
--   The LTA construction uses the row Gen gmin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean#L22-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean#L22-L78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGL.LTA.rowGen_gmin {r c m : ℕ} (a b : Fin r) (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    rowGen ℤ a b (gmin ρ κ) =
      ∑ S : Finset (Fin m), if (∀ p ∈ S, ρ p = b) then
        Polynomial.X ^ S.card * Polynomial.C (gmin (upd ρ S a) κ) else 0 := by sorry
