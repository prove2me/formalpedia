-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cw_fin
-- name    : PositivityTheory.KReal.cw_fin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:10.627939+00:00
-- url     : https://prove2.me/theorems/97696899-6f41-5636-bd4b-d4b936e55aab
-- title:
--   KReal: cw fin
-- statement:
--   The KReal construction uses the cw fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L67-L74

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
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

theorem PositivityTheory.KReal.cw_fin {r q : ℕ} (hq : q ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if r ≤ (k : ℕ) + q then c else 0) = q * c := by sorry
