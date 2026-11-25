-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_exists_int_primitive
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.exists_int_primitive
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:42.009193+00:00
-- url     : https://prove2.me/theorems/545cbdde-9c3b-4435-a462-6aac80efb5a7
-- title:
--   Fib: exists int primitive
-- statement:
--   The Fib construction uses the exists int primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L228-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L228-L265

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open Polynomial IntermediateField

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.exists_int_primitive {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    [CharZero E] [FiniteDimensional F E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hv : adjoin F (Set.range v) = ⊤) : ∃ c : ι → ℤ, F⟮∑ i, (c i : E) * v i⟯ = ⊤ := by sorry
