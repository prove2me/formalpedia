-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_support_free_of_block_subst_invariant
-- name    : ReciprocityTheory.ChartRestriction.G.T0.support_free_of_block_subst_invariant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:53:08.918866+00:00
-- url     : https://prove2.me/theorems/63d62abb-71ec-4853-9f3e-b574bbcac16f
-- title:
--   T0: support free of block subst invariant
-- statement:
--   The T0 construction uses the support free of block subst invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L160-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean#L160-L175

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

theorem ReciprocityTheory.ChartRestriction.G.T0.support_free_of_block_subst_invariant (P : KTp K D N)
    (hP : ∀ x : Fin (N + 1) → K, (aeval (fun v : TVar D N =>
      if v.1 = 0 then C (x v.2) else X v) : KTp K D N →ₐ[K] KTp K D N) P = P) :
    ∀ s ∈ P.support, degB 0 s = 0 := by sorry
