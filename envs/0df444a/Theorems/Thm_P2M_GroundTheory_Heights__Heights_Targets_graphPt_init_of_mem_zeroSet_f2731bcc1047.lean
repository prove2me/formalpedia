-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_of_mem_zeroSet_f2731bcc1047
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_of_mem_zeroSet_f2731bcc1047
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:36.843912+00:00
-- url     : https://prove2.me/theorems/10028e42-b864-5d7d-87fa-385ff99936d9
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Pt init of mem zero Set f2731bcc1047: P2 M Ground Theory Heights  Heights Targets graph Pt init of mem zero Set f2731bcc1047
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Pt init of mem zero Set f2731bcc1047 construction uses the P2 M Ground Theory Heights  Heights Targets graph Pt init of mem zero Set f2731bcc1047 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L76-L84

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

theorem P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_of_mem_zeroSet_f2731bcc1047 {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : graphPt p (Fin.init x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphPt_init_of_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_of_mem_zeroSet_f2731bcc1047
