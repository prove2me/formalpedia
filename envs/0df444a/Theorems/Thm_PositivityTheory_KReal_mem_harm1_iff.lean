-- Prove2me | Theorems.Thm_PositivityTheory_KReal_mem_harm1_iff
-- name    : PositivityTheory.KReal.mem_harm1_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:03.354815+00:00
-- url     : https://prove2.me/theorems/b6f4f023-7eaf-4827-9ffd-ad085cc8a2d1
-- title:
--   KReal: mem harm1 iff
-- statement:
--   The KReal construction uses the mem harm1 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L195-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L195-L206

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

theorem PositivityTheory.KReal.mem_harm1_iff (g : Pol p q r s) : g ∈ harm1 p q r s ↔
    ∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) g = 0 := by sorry
