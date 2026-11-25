-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_rename_swap_mem_ker_eval
-- name    : ReciprocityTheory.ChartRestriction.G.T0.rename_swap_mem_ker_eval
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:43:14.829393+00:00
-- url     : https://prove2.me/theorems/da94798a-5a3a-435f-937d-c7d00f53506f
-- title:
--   T0: rename swap mem ker eval
-- statement:
--   The T0 construction uses the rename swap mem ker eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZMultiHomogeneousDegreeSum.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZMultiHomogeneousDegreeSum.lean#L31-L36

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

theorem ReciprocityTheory.ChartRestriction.G.T0.rename_swap_mem_ker_eval (j₀ : Fin (N + 1)) (x : Fin N → Ω) (g : MvPolynomial (TVar D N) K)
    (hg : g ∈ kerP (K := K) (D := D) j₀ x) : rename swapT g ∈ kerP (K := K) (D := D) j₀ x := by sorry
