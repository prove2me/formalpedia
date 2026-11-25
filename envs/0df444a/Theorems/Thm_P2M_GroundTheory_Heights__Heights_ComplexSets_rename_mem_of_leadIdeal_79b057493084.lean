-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_rename_mem_of_leadIdeal_79b057493084
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_rename_mem_of_leadIdeal_79b057493084
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:14.479007+00:00
-- url     : https://prove2.me/theorems/6baa3909-b7f4-47b2-a891-8cad55f0495c
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets rename mem of lead Ideal 79b057493084: P2 M Ground Theory Heights  Heights Complex Sets rename mem of lead Ideal 79b057493084
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets rename mem of lead Ideal 79b057493084 construction uses the P2 M Ground Theory Heights  Heights Complex Sets rename mem of lead Ideal 79b057493084 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L49-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L49-L63

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_rename_mem_of_leadIdeal_79b057493084 (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (h : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ leadIdeal J → q = 0)
    (q : MvPolynomial u ℂ) (hq : rename Subtype.val q ∈ J) : q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«rename_mem_of_leadIdeal» := P2M_GroundTheory_Heights__Heights_ComplexSets_rename_mem_of_leadIdeal_79b057493084
