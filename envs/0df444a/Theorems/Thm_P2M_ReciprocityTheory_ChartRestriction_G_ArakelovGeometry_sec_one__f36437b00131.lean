-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sec_one__f36437b00131
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sec_one__f36437b00131
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:09.273801+00:00
-- url     : https://prove2.me/theorems/12c72068-c1bc-554f-a513-0ce965a47d94
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry sec one  f36437b00131: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry sec one  f36437b00131
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry sec one  f36437b00131 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry sec one  f36437b00131 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/RelIndexNeZeroOfMulMem.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/RelIndexNeZeroOfMulMem.lean#L49-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsMPrimeFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_RelIndexNeZeroOfMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Module
variable {Ω : Type} [Field Ω] [CharZero Ω]
variable {κ : Type} [Fintype κ]

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sec_one__f36437b00131 (x : κ → Ω) : sec ℤ x 1 = Submodule.span ℤ (Set.range x) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«sec_one'» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sec_one__f36437b00131
