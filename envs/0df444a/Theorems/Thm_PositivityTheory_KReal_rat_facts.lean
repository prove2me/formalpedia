-- Prove2me | Theorems.Thm_PositivityTheory_KReal_rat_facts
-- name    : PositivityTheory.KReal.rat_facts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:04.707608+00:00
-- url     : https://prove2.me/theorems/5abda767-b81a-5636-bd66-57b3afcef1bc
-- title:
--   KReal: rat facts
-- statement:
--   The KReal construction uses the rat facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreComb.lean#L326-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreComb.lean#L326-L343

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

theorem PositivityTheory.KReal.rat_facts {D : RealData} (h : D.Hyp) :
    (D.R : ℚ) + D.p + D.q = D.a + D.a' ∧ (D.S : ℚ) = D.p + D.q ∧ (D.P : ℚ) + D.p = D.a ∧ (D.Q : ℚ) = D.p ∧
      (D.P' : ℚ) = D.q ∧ (D.Q' : ℚ) + D.q = D.a' ∧ 2 * (nD D : ℚ) + D.a + D.a' = D.κ + 2 * D.p + 2 * D.q ∧
      2 * (mD D : ℚ) + 2 * D.p + 2 * D.q = D.κ + D.a + D.a' ∧ (D.a : ℚ) + D.a' < D.κ ∧
      2 * ((D.p : ℚ) + D.q) < D.a' ∧ (D.a' : ℚ) < D.a ∧ (0 : ℚ) ≤ D.p ∧ (0 : ℚ) ≤ D.q := by sorry
