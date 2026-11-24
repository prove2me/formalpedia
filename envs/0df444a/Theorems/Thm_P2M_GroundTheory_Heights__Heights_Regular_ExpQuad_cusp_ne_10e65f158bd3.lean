-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_cusp_ne_10e65f158bd3
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_cusp_ne_10e65f158bd3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:05.584108+00:00
-- url     : https://prove2.me/theorems/28f30f25-f713-4936-ba1e-5979643127c9
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad cusp ne 10e65f158bd3: P2 M Ground Theory Heights  Heights Regular Exp Quad cusp ne 10e65f158bd3
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad cusp ne 10e65f158bd3 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad cusp ne 10e65f158bd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L82-L83

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_cusp_ne_10e65f158bd3 {i j : Fin a} (h : i ≠ j) : Fin.castLE P.a_le i ≠ Fin.castLE P.a_le j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«cusp_ne» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_cusp_ne_10e65f158bd3
