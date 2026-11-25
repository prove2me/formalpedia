-- Prove2me | Theorems.Thm_PositivityTheory_KReal_matOp_apply
-- name    : PositivityTheory.KReal.matOp_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:59.876471+00:00
-- url     : https://prove2.me/theorems/5ca88064-f05d-489a-8bbf-ddec6cee00ab
-- title:
--   KReal: mat Op apply
-- statement:
--   The KReal construction uses the mat Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasA.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasA.lean#L57-L58

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

theorem PositivityTheory.KReal.matOp_apply (m : Matrix I I ℂ) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    matOp m Θ i = ∑ j, m i j • Θ j := by sorry
