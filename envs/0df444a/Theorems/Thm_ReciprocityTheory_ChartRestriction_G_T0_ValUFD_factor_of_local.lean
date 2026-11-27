-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_factor_of_local
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValUFD.factor_of_local
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:14:41.244405+00:00
-- url     : https://prove2.me/theorems/a324c4d5-89ec-4191-b475-f6058240f955
-- title:
--   Val UFD: factor of local
-- statement:
--   The Val UFD construction uses the factor of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L184-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L184-L274

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValUFD
variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
variable {gen : Ideal R → R}

theorem ReciprocityTheory.ChartRestriction.G.T0.ValUFD.factor_of_local (gen : Ideal R → R)
    (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    (z : F) (hz : z ≠ 0) (n : Ideal R → ℤ)
    (hn : ∀ p : Ideal R, p.IsPrime → p.height = 1 → ∃ a s : R, a ∉ p ∧ s ∉ p ∧
      z * algebraMap R F s = algebraMap R F (gen p) ^ n p * algebraMap R F a) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ n p ≠ 0}.Finite ∧
      ∃ κ : R, IsUnit κ ∧
        z = algebraMap R F κ *
          ∏ᶠ (p : Ideal R) (_ : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}),
            algebraMap R F (gen p) ^ n p := by sorry
