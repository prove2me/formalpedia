-- Prove2me | Theorems.Thm_PositivityTheory_KReal_CasGl_adC_cas
-- name    : PositivityTheory.KReal.CasGl.adC_cas
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:26.789425+00:00
-- url     : https://prove2.me/theorems/2f751f96-cd76-5412-a8df-c891eb33e5a8
-- title:
--   Cas Gl: ad C cas
-- statement:
--   The Cas Gl construction uses the ad C cas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L140-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L140-L153

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

theorem PositivityTheory.KReal.CasGl.adC_cas : ∑ k : KI r s, adC k * adC (swK k) =
    ((((r : ℝ) + s : ℝ)) : ℂ) • (1 : Matrix (PIx r s) (PIx r s) ℂ) := by sorry
