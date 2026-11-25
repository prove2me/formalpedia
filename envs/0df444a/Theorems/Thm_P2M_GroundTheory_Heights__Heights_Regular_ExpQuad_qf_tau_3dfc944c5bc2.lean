-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_tau_3dfc944c5bc2
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_tau_3dfc944c5bc2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:14.492807+00:00
-- url     : https://prove2.me/theorems/095dc1be-bfea-477b-a23d-23b76867f63c
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad qf tau 3dfc944c5bc2: P2 M Ground Theory Heights  Heights Regular Exp Quad qf tau 3dfc944c5bc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad qf tau 3dfc944c5bc2 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad qf tau 3dfc944c5bc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L85-L92

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_tau_3dfc944c5bc2 (w : Fin n → ℂ) :
    qf (P.τ w) v = qf (P.tau0 w) v +
      ∑ i, w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) * ((intQuad (P.B i) v : ℤ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«qf_tau» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_tau_3dfc944c5bc2
