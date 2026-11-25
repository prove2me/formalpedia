-- Prove2me | Theorems.Thm_PositivityTheory_KReal_mem_jHarm_iff
-- name    : PositivityTheory.KReal.mem_jHarm_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:37:53.345209+00:00
-- url     : https://prove2.me/theorems/4c492116-e5ac-5397-a0d2-b83834303964
-- title:
--   KReal: mem j Harm iff
-- statement:
--   The KReal construction uses the mem j Harm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L241-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L241-L243

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

theorem PositivityTheory.KReal.mem_jHarm_iff (g : Pol p q r s) : g ∈ jHarm p q r s ↔ g ∈ harm1 p q r s ∧
    ∀ c d : Ix r s, ¬ sameBlock c d → PI.FockOneDegW.lowOp (p := p) (q := q) c d g = 0 := by sorry
