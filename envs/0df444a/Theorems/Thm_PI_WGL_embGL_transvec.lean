-- Prove2me | Theorems.Thm_PI_WGL_embGL_transvec
-- name    : PI.WGL.embGL_transvec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:54.700801+00:00
-- url     : https://prove2.me/theorems/1b099d23-e8e3-4696-b608-82797ec8a26d
-- title:
--   WGL: emb GL transvec
-- statement:
--   The WGL construction uses the emb GL transvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliEqv.lean#L63-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliEqv.lean#L63-L80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
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

theorem PI.WGL.embGL_transvec {n : ℕ} (g : GL (Fin n) ℂ) (a b : Fin n) (t : ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b t) :
    ((embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).transpose =
      1 + Matrix.single b.castSucc a.castSucc t := by sorry
