-- Prove2me | Theorems.Thm_PositivityTheory_KReal_homogeneous_stable_first_action
-- name    : PositivityTheory.KReal.homogeneous_stable_first_action
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:38:00.747383+00:00
-- url     : https://prove2.me/theorems/7c468d96-eae4-5597-8f4a-fbff5459be5d
-- title:
--   KReal: homogeneous stable first action
-- statement:
--   The KReal construction uses the homogeneous stable first action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L281-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L281-L286

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
open Harm
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.homogeneous_stable_first_action (d : ℕ) : KSt (units (fockAct1 p q r s)) (homog (Ix p q × Ix r s) d) := by sorry
