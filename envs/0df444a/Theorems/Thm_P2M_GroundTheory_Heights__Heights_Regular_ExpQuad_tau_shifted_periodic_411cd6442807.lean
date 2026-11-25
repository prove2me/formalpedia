-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_periodic_411cd6442807
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_periodic_411cd6442807
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:26.24055+00:00
-- url     : https://prove2.me/theorems/09a0dd14-f5f0-44e8-a178-35313798e9c2
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad tau shifted periodic 411cd6442807: P2 M Ground Theory Heights  Heights Regular Exp Quad tau shifted periodic 411cd6442807
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad tau shifted periodic 411cd6442807 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad tau shifted periodic 411cd6442807 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L94-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L94-L110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_periodic_411cd6442807 (j : Fin a) (w : Fin n → ℂ) (hw : w ∈ logCover P.a_le) :
    P.tau0 (w + Pi.single (Fin.castLE P.a_le j) (2 * Real.pi * Complex.I)) = P.tau0 w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«tau_shifted_periodic» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_periodic_411cd6442807
