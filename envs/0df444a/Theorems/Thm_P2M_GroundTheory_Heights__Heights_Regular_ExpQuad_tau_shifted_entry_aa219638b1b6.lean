-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_entry_aa219638b1b6
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_entry_aa219638b1b6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:22.317832+00:00
-- url     : https://prove2.me/theorems/27ba5b16-eb7a-5782-937f-56cc00989a5a
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad tau shifted entry aa219638b1b6: P2 M Ground Theory Heights  Heights Regular Exp Quad tau shifted entry aa219638b1b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad tau shifted entry aa219638b1b6 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad tau shifted entry aa219638b1b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L114-L117

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_entry_aa219638b1b6 (w : Fin n → ℂ) (p q : Fin g) :
    P.tau0 w p q = P.τ w p q - ∑ i, w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) *
      ((P.B i p q : ℤ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«tau_shifted_entry» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_entry_aa219638b1b6
