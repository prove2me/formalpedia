-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSec_newEmb_injective_b04c3e7a8d69
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSec_newEmb_injective_b04c3e7a8d69
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:51.738725+00:00
-- url     : https://prove2.me/theorems/69d173b9-0dc3-4ce7-af98-4f8d4c828116
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Sec new Emb injective b04c3e7a8d69: P2 M Ground Theory Heights  Heights YPlus Sec new Emb injective b04c3e7a8d69
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Sec new Emb injective b04c3e7a8d69 construction uses the P2 M Ground Theory Heights  Heights YPlus Sec new Emb injective b04c3e7a8d69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSec.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSec.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSec
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSec
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_YPlusSec_newEmb_injective_b04c3e7a8d69 : Function.Injective (newEmb D) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSec».«newEmb_injective» := P2M_GroundTheory_Heights__Heights_YPlusSec_newEmb_injective_b04c3e7a8d69
