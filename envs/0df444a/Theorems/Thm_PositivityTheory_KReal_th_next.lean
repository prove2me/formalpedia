-- Prove2me | Theorems.Thm_PositivityTheory_KReal_th_next
-- name    : PositivityTheory.KReal.th_next
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:07.615547+00:00
-- url     : https://prove2.me/theorems/e94ee06a-1c64-547b-aa26-a449b86563d5
-- title:
--   KReal: th next
-- statement:
--   The KReal construction uses the th next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSplit.lean#L103-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSplit.lean#L103-L128

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

theorem PositivityTheory.KReal.th_next (c : ℂ) (c0 : ℚ) (hc : c = c0) (d0 : ℕ)
    (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) :
    (homog (Ix p q × Ix r s) (d0 + 2)).map (thMkC p q r s c) ≤
      (harm1 p q r s ⊓ polChi p q r s c ⊓ homog (Ix p q × Ix r s) (d0 + 2)).map (thMkC p q r s c) := by sorry
