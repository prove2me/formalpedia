-- Prove2me | Theorems.Thm_PositivityTheory_KReal_CasGl_adad_apply
-- name    : PositivityTheory.KReal.CasGl.adad_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:06.194851+00:00
-- url     : https://prove2.me/theorems/0f8f5a2c-1d95-597b-abc9-a606c37bd133
-- title:
--   Cas Gl: adad apply
-- statement:
--   The Cas Gl construction uses the adad apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L127-L132

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

theorem PositivityTheory.KReal.CasGl.adad_apply (a b e f : Ix r s) {Z : Mat r s} (hZ : IsPC Z) :
    ((Eab a b * (Eab b a * Z - Z * Eab b a) - (Eab b a * Z - Z * Eab b a) * Eab a b : Mat r s)) e f =
      ((if e = a then 1 else 0) + (if f = b then 1 else 0)) * Z e f := by sorry
