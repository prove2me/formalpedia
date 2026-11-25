-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscOmL_disc_local
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL.disc_local
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:08.76041+00:00
-- url     : https://prove2.me/theorems/3967e4b2-1fbf-4735-ba97-bb996c109e89
-- title:
--   HDisc Om L: disc local
-- statement:
--   The HDisc Om L construction uses the disc local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DiscLocal.lean#L25-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DiscLocal.lean#L25-L127

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

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL.disc_local (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c) (hli : LinearIndependent F b)
    (hb : ∀ k c, ∀ w ∈ HNm.OverR R F (L c) p, 0 ≤ w (b k c) + (n c w : WithTop ℤ)) :
    ∃ a s : R, s ∉ p ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
        algebraMap R F g ^ (2 * ∑ c, ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
          (_ : w ∈ HNm.OverR R F (L c) p), (HNm.fz F w : ℤ) * n c w) * algebraMap R F s =
        algebraMap R F a := by sorry
