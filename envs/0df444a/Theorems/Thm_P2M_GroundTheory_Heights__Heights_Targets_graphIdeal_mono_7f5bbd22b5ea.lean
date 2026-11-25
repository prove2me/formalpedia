-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_mono_7f5bbd22b5ea
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_mono_7f5bbd22b5ea
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:40:35.244838+00:00
-- url     : https://prove2.me/theorems/910eb04b-1342-4170-9819-db5236c91695
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Ideal mono 7f5bbd22b5ea: P2 M Ground Theory Heights  Heights Targets graph Ideal mono 7f5bbd22b5ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Ideal mono 7f5bbd22b5ea construction uses the P2 M Ground Theory Heights  Heights Targets graph Ideal mono 7f5bbd22b5ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L122-L124

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

theorem P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_mono_7f5bbd22b5ea {J W : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) (h : J ≤ W) :
    graphIdeal J p ≤ graphIdeal W p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphIdeal_mono» := P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_mono_7f5bbd22b5ea
