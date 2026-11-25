-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inl_33cc3b99f307
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inl_33cc3b99f307
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:29.260018+00:00
-- url     : https://prove2.me/theorems/5655518e-6052-51b9-99ac-a0444f5f9de7
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inr inl 33cc3b99f307: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inr inl 33cc3b99f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inr inl 33cc3b99f307 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inr inl 33cc3b99f307 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L32-L34

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inl_33cc3b99f307 (f : K₂ → M) (k : K) : Function.extend (Sum.inr : K₂ → K ⊕ K₂) f 0 (Sum.inl k) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«extend_inr_inl» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inl_33cc3b99f307
