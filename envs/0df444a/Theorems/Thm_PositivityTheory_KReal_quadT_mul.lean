-- Prove2me | Theorems.Thm_PositivityTheory_KReal_quadT_mul
-- name    : PositivityTheory.KReal.quadT_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:21.186154+00:00
-- url     : https://prove2.me/theorems/4de22fac-afa5-49f8-a9db-df36491660e8
-- title:
--   KReal: quad T mul
-- statement:
--   The KReal construction uses the quad T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean#L34-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean#L34-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PositivityTheory PositivityTheory.KReal
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Ring E] [Algebra ℂ E]

theorem PositivityTheory.KReal.quadT_mul (R L : ι → E)
    (hLR : ∀ a b, L a * R b = R b * L a + if a = b then 1 else 0) (A B : Matrix ι ι ℂ) :
    quadT R L A * quadT R L B = quartT R L A B + quadT R L (A * B) := by sorry
