-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_relIndex_ne_zero_of_mul_mem
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.relIndex_ne_zero_of_mul_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:03:00.391283+00:00
-- url     : https://prove2.me/theorems/0b213eb1-3aa8-40b4-8649-94949b35604d
-- title:
--   Arakelov Geometry: rel Index ne zero of mul mem
-- statement:
--   The Arakelov Geometry construction uses the rel Index ne zero of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/RelIndexNeZeroOfMulMem.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/RelIndexNeZeroOfMulMem.lean#L20-L31

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.relIndex_ne_zero_of_mul_mem {H K : Submodule ℤ Ω} (hK : K.FG) {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ u ∈ K, (M : Ω) * u ∈ H) : H.toAddSubgroup.relIndex K.toAddSubgroup ≠ 0 := by sorry
