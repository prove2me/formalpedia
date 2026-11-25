-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_one_block
-- name    : ReciprocityTheory.ChartRestriction.G.T0.one_block
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:34.574444+00:00
-- url     : https://prove2.me/theorems/01da124a-8a7f-4758-b7c6-b4c5da4eecdc
-- title:
--   T0: one block
-- statement:
--   The T0 construction uses the one block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L77-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L77-L135

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
variable {K : Type} [Field K] [CharZero K] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.one_block (b : Fin (D + 1)) (z : KTf K D N)
    (hz : ∀ u : Kˣ, sigF (K := K) (D := D) (N := N) b u z = z)
    (p q : KTp K D N) (hq : q ≠ 0)
    (hpq : algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q) :
    ∃ k, compB b k q ≠ 0 ∧ algebraMap (KTp K D N) (KTf K D N) (compB b k p) =
      z * algebraMap (KTp K D N) (KTf K D N) (compB b k q) := by sorry
