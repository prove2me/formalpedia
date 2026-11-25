-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ringKrullDim_graphIdeal_a824ae9cd5f3
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ringKrullDim_graphIdeal_a824ae9cd5f3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:22.934807+00:00
-- url     : https://prove2.me/theorems/28ebb497-1a0b-5eb8-ac9f-02986276f45b
-- title:
--   P2 M Ground Theory Heights  Heights Targets ring Krull Dim graph Ideal a824ae9cd5f3: P2 M Ground Theory Heights  Heights Targets ring Krull Dim graph Ideal a824ae9cd5f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets ring Krull Dim graph Ideal a824ae9cd5f3 construction uses the P2 M Ground Theory Heights  Heights Targets ring Krull Dim graph Ideal a824ae9cd5f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L86-L94

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ringKrullDim_graphIdeal_a824ae9cd5f3 (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J p) = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ringKrullDim_graphIdeal» := P2M_GroundTheory_Heights__Heights_Targets_ringKrullDim_graphIdeal_a824ae9cd5f3
