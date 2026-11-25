-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sigF_alg
-- name    : ReciprocityTheory.ChartRestriction.G.T0.sigF_alg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:41:59.905367+00:00
-- url     : https://prove2.me/theorems/17800ddf-ec6b-52e9-a0fb-d5d7d3522e94
-- title:
--   T0: sig F alg
-- statement:
--   The T0 construction uses the sig F alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L70-L75

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

theorem ReciprocityTheory.ChartRestriction.G.T0.sigF_alg (b : Fin (D + 1)) (u : Kˣ) (g : KTp K D N) :
    sigF (K := K) (D := D) (N := N) b u (algebraMap (KTp K D N) (KTf K D N) g) =
      algebraMap (KTp K D N) (KTf K D N) (sigP b u g) := by sorry
