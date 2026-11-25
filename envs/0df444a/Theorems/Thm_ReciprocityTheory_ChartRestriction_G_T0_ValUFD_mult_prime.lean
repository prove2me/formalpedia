-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_mult_prime
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValUFD.mult_prime
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:27.93209+00:00
-- url     : https://prove2.me/theorems/583e6c75-3f79-5bd5-b109-06faf76beadd
-- title:
--   Val UFD: mult prime
-- statement:
--   The Val UFD construction uses the mult prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L102-L109

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValUFD.mult_prime (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    {p : Ideal R} (hp : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}) {q : R} (hq : Prime q) :
    multiplicity (gen p) q = if p = Ideal.span {q} then 1 else 0 := by sorry
