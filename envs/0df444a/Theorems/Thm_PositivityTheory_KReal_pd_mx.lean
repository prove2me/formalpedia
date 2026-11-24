-- Prove2me | Theorems.Thm_PositivityTheory_KReal_pd_mx
-- name    : PositivityTheory.KReal.pd_mx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:06.86035+00:00
-- url     : https://prove2.me/theorems/a07e4739-a4bb-4e5f-9685-f0e32a6e1c0b
-- title:
--   KReal: pd mx
-- statement:
--   The KReal construction uses the pd mx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean#L97-L104

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
variable {σ : Type*} [DecidableEq σ]

theorem PositivityTheory.KReal.pd_mx (a b : σ) :
    ((pderiv a).toLinearMap * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * (pderiv a).toLinearMap + if a = b then 1 else 0 := by sorry
