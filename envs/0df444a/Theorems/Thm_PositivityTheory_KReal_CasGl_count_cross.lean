-- Prove2me | Theorems.Thm_PositivityTheory_KReal_CasGl_count_cross
-- name    : PositivityTheory.KReal.CasGl.count_cross
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:52.026382+00:00
-- url     : https://prove2.me/theorems/3315fe64-e167-554f-8aca-2d430acd2210
-- title:
--   Cas Gl: count cross
-- statement:
--   The Cas Gl construction uses the count cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L134-L138

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
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
open PositivityTheory.KReal.CasGl
variable {r s : ℕ}

theorem PositivityTheory.KReal.CasGl.count_cross {e f : Ix r s} (h : ¬ sameBlock e f) :
    (∑ a : Ix r s, ∑ b : Ix r s, if sameBlock a b then
      ((if e = a then 1 else 0) + (if f = b then 1 else 0) : ℂ) else 0) = (r : ℂ) + s := by sorry
