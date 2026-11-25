-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inr_28b0ddbfc99d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inr_28b0ddbfc99d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:08.099302+00:00
-- url     : https://prove2.me/theorems/5132dff7-a2f2-46de-abd5-8bcf50eda474
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inr inr 28b0ddbfc99d: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inr inr 28b0ddbfc9
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inr inr 28b0ddbfc99d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inr inr 28b0ddbfc99d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L29-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K K₂ M : Type*} [Zero M]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inr_28b0ddbfc99d (f : K₂ → M) (k : K₂) : Function.extend (Sum.inr : K₂ → K ⊕ K₂) f 0 (Sum.inr k) = f k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«extend_inr_inr» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inr_28b0ddbfc99d
