-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_splitFirst_0909c034ee7a
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_splitFirst_0909c034ee7a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:45.693234+00:00
-- url     : https://prove2.me/theorems/d3ba904f-11f5-4cc9-9ac1-ae3bc017368e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice join First split First 0909c034ee7a: P2 M Ground Theory Heights  Heights Chart Choice join First split First 0909c034ee7a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice join First split First 0909c034ee7a construction uses the P2 M Ground Theory Heights  Heights Chart Choice join First split First 0909c034ee7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L27-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartChoice
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChoice
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_splitFirst_0909c034ee7a (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoice».«joinFirst_splitFirst» := P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_splitFirst_0909c034ee7a
