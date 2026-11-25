-- Prove2me | Theorems.Thm_PositivityTheory_KReal_CasGl_adC_mul
-- name    : PositivityTheory.KReal.CasGl.adC_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:14.202844+00:00
-- url     : https://prove2.me/theorems/2b1362f4-289f-5783-be8d-07ee9ef38bdb
-- title:
--   Cas Gl: ad C mul
-- statement:
--   The Cas Gl construction uses the ad C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L113-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L113-L125

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

theorem PositivityTheory.KReal.CasGl.adC_mul (k k' : KI r s) (j i : PIx r s) :
    (adC k * adC k') j i =
      ((Eab k.1.1 k.1.2 * (Eab k'.1.1 k'.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k'.1.1 k'.1.2) -
        (Eab k'.1.1 k'.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k'.1.1 k'.1.2) * Eab k.1.1 k.1.2 :
          Mat r s)) j.1.1 j.1.2 := by sorry
