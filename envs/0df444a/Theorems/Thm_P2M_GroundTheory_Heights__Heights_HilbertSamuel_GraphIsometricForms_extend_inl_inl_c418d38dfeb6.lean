-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inl_inl_c418d38dfeb6
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inl_inl_c418d38dfeb6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:52.021681+00:00
-- url     : https://prove2.me/theorems/3c084db5-0b6b-48d1-be08-42d49681ae9b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inl inl c418d38dfeb6: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inl inl c418d38dfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inl inl c418d38dfeb6 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms extend inl inl c418d38dfeb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L22-L23

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inl_inl_c418d38dfeb6 (f : K → M) (k : K) : Function.extend (Sum.inl : K → K ⊕ K₂) f 0 (Sum.inl k) = f k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«extend_inl_inl» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inl_inl_c418d38dfeb6
