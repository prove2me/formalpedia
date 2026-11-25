-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorOneComponent_isClosed_zeroSet_e95e7da77948
-- name    : P2M_GroundTheory_Heights__Heights_DivisorOneComponent_isClosed_zeroSet_e95e7da77948
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:07.854164+00:00
-- url     : https://prove2.me/theorems/11d618ba-8d72-48eb-b642-8d7ed7b42fdb
-- title:
--   P2 M Ground Theory Heights  Heights Divisor One Component is Closed zero Set e95e7da77948: P2 M Ground Theory Heights  Heights Divisor One Component is Closed zero Set e95e7da77948
-- statement:
--   The P2 M Ground Theory Heights  Heights Divisor One Component is Closed zero Set e95e7da77948 construction uses the P2 M Ground Theory Heights  Heights Divisor One Component is Closed zero Set e95e7da77948 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorOneComponent.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorOneComponent.lean#L19-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorOneComponent
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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorOneComponent

theorem P2M_GroundTheory_Heights__Heights_DivisorOneComponent_isClosed_zeroSet_e95e7da77948 {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DivisorOneComponent».«isClosed_zeroSet» := P2M_GroundTheory_Heights__Heights_DivisorOneComponent_isClosed_zeroSet_e95e7da77948
