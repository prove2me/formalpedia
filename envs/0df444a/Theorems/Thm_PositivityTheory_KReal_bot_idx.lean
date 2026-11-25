-- Prove2me | Theorems.Thm_PositivityTheory_KReal_bot_idx
-- name    : PositivityTheory.KReal.bot_idx
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:50.118297+00:00
-- url     : https://prove2.me/theorems/268f8446-657f-4174-ad7a-7876cf4ff461
-- title:
--   KReal: bot idx
-- statement:
--   The KReal construction uses the bot idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreComb.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreComb.lean#L25-L38

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreComb
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

theorem PositivityTheory.KReal.bot_idx {N : ℕ} (f g : Fin N → ℚ) (j : Fin N) (hdom : ∀ j', j < j' → g j' ≤ g j)
    (hg : g j = f j - 1) (hg' : ∀ j', j' ≠ j → g j' = f j') (hf : ∀ j', j < j' → f j' = f j) :
    (j : ℕ) + 1 = N := by sorry
