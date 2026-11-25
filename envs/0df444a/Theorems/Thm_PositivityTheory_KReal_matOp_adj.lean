-- Prove2me | Theorems.Thm_PositivityTheory_KReal_matOp_adj
-- name    : PositivityTheory.KReal.matOp_adj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:57.9877+00:00
-- url     : https://prove2.me/theorems/7409e869-c34d-58bd-84de-bda09be2ecf2
-- title:
--   KReal: mat Op adj
-- statement:
--   The KReal construction uses the mat Op adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasA.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasA.lean#L63-L68

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA
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
variable {I : Type} [Fintype I] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem PositivityTheory.KReal.matOp_adj (m : Matrix I I ℂ) (x y : PiLp 2 (fun _ : I => V)) :
    ⟪matOp m x, y⟫_ℂ = ⟪x, matOp mᴴ y⟫_ℂ := by sorry
