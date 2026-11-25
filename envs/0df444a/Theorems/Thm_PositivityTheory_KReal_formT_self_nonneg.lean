-- Prove2me | Theorems.Thm_PositivityTheory_KReal_formT_self_nonneg
-- name    : PositivityTheory.KReal.formT_self_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:05.463051+00:00
-- url     : https://prove2.me/theorems/967621ff-90b5-5e12-99c1-70255fb86bae
-- title:
--   KReal: form T self nonneg
-- statement:
--   The KReal construction uses the form T self nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasC.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasC.lean#L47-L52

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem PositivityTheory.KReal.formT_self_nonneg (a : (J → I) → V) : 0 ≤ (formT a a).re := by sorry
