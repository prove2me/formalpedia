-- Prove2me | Theorems.Thm_PositivityTheory_KReal_star_cas_mk
-- name    : PositivityTheory.KReal.star_cas_mk
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:09:12.636654+00:00
-- url     : https://prove2.me/theorems/63512118-6e38-49d2-a74b-9ea0640c3b75
-- title:
--   KReal: star cas mk
-- statement:
--   The KReal construction uses the star cas mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreStar.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreStar.lean#L64-L72

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreRoot
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSupp
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreStar
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

theorem PositivityTheory.KReal.star_cas_mk {p q r s : ℕ} (c τ : ℂ) (g : Pol p q r s) :
    casK (units (thAct p q r s c τ)) (thMkC p q r s c g) =
      thMkC p q r s c (casK (units (twAct p q r s τ)) g) := by sorry
