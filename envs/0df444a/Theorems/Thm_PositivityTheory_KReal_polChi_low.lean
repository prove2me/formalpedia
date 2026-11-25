-- Prove2me | Theorems.Thm_PositivityTheory_KReal_polChi_low
-- name    : PositivityTheory.KReal.polChi_low
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:37:53.761397+00:00
-- url     : https://prove2.me/theorems/50a3317e-4211-5432-b670-a05f7b2c2536
-- title:
--   KReal: pol Chi low
-- statement:
--   The KReal construction uses the pol Chi low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L330-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L330-L344

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

theorem PositivityTheory.KReal.polChi_low (c0 : ℂ) {c d : Ix r s} (hcd : ¬ sameBlock c d) {g : Pol p q r s}
    (hg : g ∈ polChi p q r s c0) : PI.FockOneDegW.lowOp (p := p) (q := q) c d g ∈ polChi p q r s c0 := by sorry
