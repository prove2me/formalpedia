-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_factor_int
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValUFD.factor_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:25.258118+00:00
-- url     : https://prove2.me/theorems/63e6f249-9a4e-5c5a-9caf-2a76dcb9cee3
-- title:
--   Val UFD: factor int
-- statement:
--   The Val UFD construction uses the factor int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L111-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L111-L182

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValUFD.factor_int (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    (r : R) (hr : r ≠ 0) :
    ({p : Ideal R | p.IsPrime ∧ p.height = 1} ∩ {p | multiplicity (gen p) r ≠ 0}).Finite ∧
      ∃ κ : R, IsUnit κ ∧ algebraMap R F r = algebraMap R F κ *
        ∏ᶠ (p : Ideal R) (_ : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}),
          algebraMap R F (gen p) ^ (multiplicity (gen p) r : ℤ) := by sorry
