-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_update_comp_swap_7f6a686cf33e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_update_comp_swap_7f6a686cf33e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:41.774361+00:00
-- url     : https://prove2.me/theorems/85040f5a-a26f-4a57-bba8-8a846b9f9e87
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IMultilin update comp swap 7f6a686cf33e: P2 M Ground Theory Heights  Heights Inter Thm IMultilin update comp swap 7f6a686cf33e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IMultilin update comp swap 7f6a686cf33e construction uses the P2 M Ground Theory Heights  Heights Inter Thm IMultilin update comp swap 7f6a686cf33e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIMultilin.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIMultilin.lean#L24-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIMultilin
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.ThmIMultilin
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_update_comp_swap_7f6a686cf33e {m : ℕ} (L : Fin (m + 1) → HermLine ι) (j : Fin (m + 1)) (X : HermLine ι) :
    Function.update L j X ∘ Equiv.swap j (Fin.last m) =
      Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIMultilin».«update_comp_swap» := P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_update_comp_swap_7f6a686cf33e
