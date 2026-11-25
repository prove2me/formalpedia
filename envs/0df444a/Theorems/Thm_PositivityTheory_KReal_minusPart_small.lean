-- Prove2me | Theorems.Thm_PositivityTheory_KReal_minusPart_small
-- name    : PositivityTheory.KReal.minusPart_small
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:51.529915+00:00
-- url     : https://prove2.me/theorems/11706243-f912-55c5-b3cc-f06c8ea63c76
-- title:
--   KReal: minus Part small
-- statement:
--   The KReal construction uses the minus Part small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSplit.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSplit.lean#L20-L24

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSplit
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
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.minusPart_small {σ : Type} (A : Module.End ℂ (MvPolynomial σ ℂ)) {d : ℕ} (hd : d < 2)
    {Q : MvPolynomial σ ℂ} (hQ : Q ∈ homog σ d) : minusPart A Q = 0 := by sorry
