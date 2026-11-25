-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_chiP_rename_swap
-- name    : ReciprocityTheory.ChartRestriction.G.T0.chiP_rename_swap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:42:51.201447+00:00
-- url     : https://prove2.me/theorems/9516ca52-7009-44bb-9c52-c5dd4cf66a0e
-- title:
--   T0: chi P rename swap
-- statement:
--   The T0 construction uses the chi P rename swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZMultiHomogeneousDegreeSum.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZMultiHomogeneousDegreeSum.lean#L17-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.chiP_rename_swap (j₀ : Fin (N + 1)) (x : Fin N → Ω) (g : MvPolynomial (TVar D N) K) :
    chiP (K := K) j₀ x (rename swapT g) = rename swapS (chiP (K := K) j₀ x g) := by sorry
