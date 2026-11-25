-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_support_compB
-- name    : ReciprocityTheory.ChartRestriction.G.T0.mem_support_compB
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:20.538616+00:00
-- url     : https://prove2.me/theorems/af3a7866-1ac8-4e9f-8c84-28161cd38784
-- title:
--   T0: mem support comp B
-- statement:
--   The T0 construction uses the mem support comp B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L35-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
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
variable {K : Type} [Field K] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.mem_support_compB {b : Fin (D + 1)} {k : ℕ} {p : MvPolynomial (TVar D N) K}
    {t : TVar D N →₀ ℕ} (ht : t ∈ (compB b k p).support) : t ∈ p.support ∧ degB b t = k := by sorry
