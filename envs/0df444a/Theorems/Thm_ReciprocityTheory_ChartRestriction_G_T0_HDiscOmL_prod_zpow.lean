-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscOmL_prod_zpow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL.prod_zpow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:23.465368+00:00
-- url     : https://prove2.me/theorems/472e02e8-56bc-4e9b-a544-5077e505b44a
-- title:
--   HDisc Om L: prod zpow
-- statement:
--   The HDisc Om L construction uses the prod zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DiscLocal.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DiscLocal.lean#L19-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL
open IsDedekindDomain IsLocalRing Module
variable {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]
omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R F]

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL.prod_zpow {κ G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset κ)
    (f : κ → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by sorry
