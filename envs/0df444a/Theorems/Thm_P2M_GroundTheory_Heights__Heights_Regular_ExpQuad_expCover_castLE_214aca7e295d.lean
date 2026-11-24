-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_castLE_214aca7e295d
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_castLE_214aca7e295d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:20.681165+00:00
-- url     : https://prove2.me/theorems/8cb3eeeb-9f9e-42f1-b6f6-ce73840afc86
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad exp Cover cast LE 214aca7e295d: P2 M Ground Theory Heights  Heights Regular Exp Quad exp Cover cast LE 214aca7e295d
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad exp Cover cast LE 214aca7e295d construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad exp Cover cast LE 214aca7e295d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L169-L171

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_castLE_214aca7e295d (w : Fin n → ℂ) (i : Fin a) :
    expCover a w (Fin.castLE P.a_le i) = Complex.exp (w (Fin.castLE P.a_le i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«expCover_castLE» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_castLE_214aca7e295d
