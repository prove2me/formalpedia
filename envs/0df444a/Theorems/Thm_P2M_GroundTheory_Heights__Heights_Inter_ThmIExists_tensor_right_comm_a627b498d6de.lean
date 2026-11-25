-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_tensor_right_comm_a627b498d6de
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_tensor_right_comm_a627b498d6de
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:40.132341+00:00
-- url     : https://prove2.me/theorems/192070cd-0178-5db6-b56e-73991c477beb
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists tensor right comm a627b498d6de: P2 M Ground Theory Heights  Heights Inter Thm IExists tensor right comm a627b498d6de
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists tensor right comm a627b498d6de construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists tensor right comm a627b498d6de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L23-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_tensor_right_comm_a627b498d6de (A B C : HermLine ι) :
    (A.tensor B).tensor C = (A.tensor C).tensor B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«tensor_right_comm» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_tensor_right_comm_a627b498d6de
