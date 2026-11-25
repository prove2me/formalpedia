-- Prove2me | Theorems.Thm_PositivityTheory_KReal_CasGl_kc_mul
-- name    : PositivityTheory.KReal.CasGl.kc_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:45.700442+00:00
-- url     : https://prove2.me/theorems/6324bb21-9b15-534c-97d9-6c78040a9e7d
-- title:
--   Cas Gl: kc mul
-- statement:
--   The Cas Gl construction uses the kc mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L86-L94

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

theorem PositivityTheory.KReal.CasGl.kc_mul {Z W : Mat r s} (hZ : IsPC Z) (hW : IsPC W) : IsKC (Z * W) := by sorry
