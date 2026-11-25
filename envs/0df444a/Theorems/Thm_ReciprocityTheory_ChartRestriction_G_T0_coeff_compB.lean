-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeff_compB
-- name    : ReciprocityTheory.ChartRestriction.G.T0.coeff_compB
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:45:59.382399+00:00
-- url     : https://prove2.me/theorems/b1e9bd54-2dac-43d7-a6de-5134ffddeae0
-- title:
--   T0: coeff comp B
-- statement:
--   The T0 construction uses the coeff comp B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L18-L33

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

theorem ReciprocityTheory.ChartRestriction.G.T0.coeff_compB (b : Fin (D + 1)) (k : ℕ) (p : MvPolynomial (TVar D N) K) (t : TVar D N →₀ ℕ) :
    coeff t (compB b k p) = if degB b t = k then coeff t p else 0 := by sorry
