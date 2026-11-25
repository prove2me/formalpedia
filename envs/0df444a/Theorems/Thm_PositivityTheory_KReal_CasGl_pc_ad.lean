-- Prove2me | Theorems.Thm_PositivityTheory_KReal_CasGl_pc_ad
-- name    : PositivityTheory.KReal.CasGl.pc_ad
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:15.669273+00:00
-- url     : https://prove2.me/theorems/af8a973d-7caa-563f-96c6-28580231fb4a
-- title:
--   Cas Gl: pc ad
-- statement:
--   The Cas Gl construction uses the pc ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L74-L84

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

theorem PositivityTheory.KReal.CasGl.pc_ad {a b : Ix r s} (h : sameBlock a b) {Z : Mat r s} (hZ : IsPC Z) :
    IsPC (Eab a b * Z - Z * Eab a b) := by sorry
