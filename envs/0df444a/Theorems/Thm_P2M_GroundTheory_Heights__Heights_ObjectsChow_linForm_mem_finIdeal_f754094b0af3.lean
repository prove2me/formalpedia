-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_linForm_mem_finIdeal_f754094b0af3
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_linForm_mem_finIdeal_f754094b0af3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:26.688111+00:00
-- url     : https://prove2.me/theorems/524e0eb8-6829-4361-ad67-a5d6b91e0839
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow lin Form mem fin Ideal f754094b0af3: P2 M Ground Theory Heights  Heights Objects Chow lin Form mem fin Ideal f754094b0af3
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow lin Form mem fin Ideal f754094b0af3 construction uses the P2 M Ground Theory Heights  Heights Objects Chow lin Form mem fin Ideal f754094b0af3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_linForm_mem_finIdeal_f754094b0af3 (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ) :
    linForm u ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P ↔ IndefiniteRowSideFullHecke.ArithBezout.linForm u ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«linForm_mem_finIdeal» := P2M_GroundTheory_Heights__Heights_ObjectsChow_linForm_mem_finIdeal_f754094b0af3
