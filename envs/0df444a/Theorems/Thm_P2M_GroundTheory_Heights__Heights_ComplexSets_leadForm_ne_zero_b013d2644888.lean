-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_leadForm_ne_zero_b013d2644888
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_leadForm_ne_zero_b013d2644888
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:29.645792+00:00
-- url     : https://prove2.me/theorems/6ac38ca6-1e27-487c-ae10-788dfacc75ff
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets lead Form ne zero b013d2644888: P2 M Ground Theory Heights  Heights Complex Sets lead Form ne zero b013d2644888
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets lead Form ne zero b013d2644888 construction uses the P2 M Ground Theory Heights  Heights Complex Sets lead Form ne zero b013d2644888 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L14-L21

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_leadForm_ne_zero_b013d2644888 {f : MvPolynomial (Fin n) ℂ} (hf : f ≠ 0) : leadForm f ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«leadForm_ne_zero» := P2M_GroundTheory_Heights__Heights_ComplexSets_leadForm_ne_zero_b013d2644888
