-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_subsingleton_of_not_le_5e934b8b52e3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_subsingleton_of_not_le_5e934b8b52e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:08.861916+00:00
-- url     : https://prove2.me/theorems/ff78bf11-7275-4446-87c3-c6da81499173
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR localized Quot subsingleton of not le 5e934b8b52e3: P2 M Ground Theory Heights  Heights Numbers DVR localized Quot subsingleton of not le 5e934b8b52e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR localized Quot subsingleton of not le 5e934b8b52e3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR localized Quot subsingleton of not le 5e934b8b52e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_subsingleton_of_not_le_5e934b8b52e3 (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«localizedQuot_subsingleton_of_not_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_subsingleton_of_not_le_5e934b8b52e3
