-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_vars_leadForm_subset_cd5959c51b0f
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_vars_leadForm_subset_cd5959c51b0f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:05.728177+00:00
-- url     : https://prove2.me/theorems/a1326b10-d323-5245-b87e-d0959f0d190f
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets vars lead Form subset cd5959c51b0f: P2 M Ground Theory Heights  Heights Complex Sets vars lead Form subset cd5959c51b0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets vars lead Form subset cd5959c51b0f construction uses the P2 M Ground Theory Heights  Heights Complex Sets vars lead Form subset cd5959c51b0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L23-L32

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_vars_leadForm_subset_cd5959c51b0f (f : MvPolynomial (Fin n) ℂ) : (leadForm f).vars ⊆ f.vars := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«vars_leadForm_subset» := P2M_GroundTheory_Heights__Heights_ComplexSets_vars_leadForm_subset_cd5959c51b0f
