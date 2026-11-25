-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_ae_eval_ne_zero_80133a975faf
-- name    : P2M_GroundTheory_Heights__Heights_CutOffDominated_ae_eval_ne_zero_80133a975faf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:22:15.283294+00:00
-- url     : https://prove2.me/theorems/e54c6ab0-0356-5ddf-ab76-7a9b5f6e5ef0
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Dominated ae eval ne zero 80133a975faf: P2 M Ground Theory Heights  Heights Cut Off Dominated ae eval ne zero 80133a975faf
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Dominated ae eval ne zero 80133a975faf construction uses the P2 M Ground Theory Heights  Heights Cut Off Dominated ae eval ne zero 80133a975faf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffDominated.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffDominated.lean#L34-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffDominated
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CutOffDominated_ae_eval_ne_zero_80133a975faf {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffDominated».«ae_eval_ne_zero» := P2M_GroundTheory_Heights__Heights_CutOffDominated_ae_eval_ne_zero_80133a975faf
