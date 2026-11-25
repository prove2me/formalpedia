-- Prove2me | Theorems.Thm_PositivityTheory_KReal_th_small
-- name    : PositivityTheory.KReal.th_small
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:45.905412+00:00
-- url     : https://prove2.me/theorems/a0b835c2-beb6-586c-94b8-92983425b152
-- title:
--   KReal: th small
-- statement:
--   The KReal construction uses the th small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSplit.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSplit.lean#L86-L90

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

theorem PositivityTheory.KReal.th_small (c : ℂ) (c0 : ℚ) (hc : c = c0) (d : ℕ)
    (hd : (d : ℚ) < degW (cPair r s) (fun _ : Ix p q => c0)) {g : Pol p q r s}
    (hg : g ∈ homog (Ix p q × Ix r s) d) : thMkC p q r s c g = 0 := by sorry
