-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_multi_pres
-- name    : ReciprocityTheory.ChartRestriction.G.T0.multi_pres
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:20.32893+00:00
-- url     : https://prove2.me/theorems/349c790c-1f05-48d2-8267-2ac729fbdcbe
-- title:
--   T0: multi pres
-- statement:
--   The T0 construction uses the multi pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L177-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L177-L219

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

theorem ReciprocityTheory.ChartRestriction.G.T0.multi_pres (z : KTf K D N)
    (hz : ∀ (b : Fin (D + 1)) (u : Kˣ), sigF (K := K) (D := D) (N := N) b u z = z)
    (p q : KTp K D N) (hq : q ≠ 0)
    (hpq : algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q)
    (hp0 : ∀ s ∈ p.support, degB 0 s = 0) (hq0 : ∀ s ∈ q.support, degB 0 s = 0) :
    ∃ a b : KTp K D N, b ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) a = z * algebraMap (KTp K D N) (KTf K D N) b ∧
      ∃ m : Fin (D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
        ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b := by sorry
