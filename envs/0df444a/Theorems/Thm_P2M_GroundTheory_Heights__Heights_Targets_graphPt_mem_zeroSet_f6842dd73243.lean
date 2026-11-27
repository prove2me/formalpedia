-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphPt_mem_zeroSet_f6842dd73243
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphPt_mem_zeroSet_f6842dd73243
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:10.700439+00:00
-- url     : https://prove2.me/theorems/16849c4b-a4e0-4b0d-9697-a77ce51d5cfc
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Pt mem zero Set f6842dd73243: P2 M Ground Theory Heights  Heights Targets graph Pt mem zero Set f6842dd73243
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Pt mem zero Set f6842dd73243 construction uses the P2 M Ground Theory Heights  Heights Targets graph Pt mem zero Set f6842dd73243 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L63-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_graphPt_mem_zeroSet_f6842dd73243 {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : graphPt p x ∈ zeroSet (graphIdeal J p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphPt_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_Targets_graphPt_mem_zeroSet_f6842dd73243
