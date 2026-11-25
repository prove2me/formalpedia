-- Prove2me | Theorems.Thm_PositivityTheory_KReal_supp_gR
-- name    : PositivityTheory.KReal.supp_gR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:10.513291+00:00
-- url     : https://prove2.me/theorems/e43b4dfc-de3c-40d0-a888-b1df5895f7b5
-- title:
--   KReal: supp g R
-- statement:
--   The KReal construction uses the supp g R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L283-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L283-L297

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSupp
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
variable {p q r s : ℕ} {ν : Ix r s → ℚ} {g : Pol p q r s}

theorem PositivityTheory.KReal.supp_gR (hg : IsHW (fockAct2 p q r s) ν g) {c d : Ix r s} (h : posC c d) :
    PI.FJMP.gR (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => (a, d))
      (fun a => linePos ((a, c) : Ln p q r s)) g = 0 := by sorry
