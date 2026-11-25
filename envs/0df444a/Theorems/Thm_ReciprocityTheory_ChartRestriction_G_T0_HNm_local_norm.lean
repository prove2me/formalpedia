-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HNm_local_norm
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HNm.local_norm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:51:19.215036+00:00
-- url     : https://prove2.me/theorems/efeefb72-7409-5da8-a64d-448f3df832cd
-- title:
--   HNm: local norm
-- statement:
--   The HNm construction uses the local norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormB.lean#L27-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormB.lean#L27-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HNm
open IsDedekindDomain IsLocalRing
variable {R F L : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L]

theorem ReciprocityTheory.ChartRestriction.G.T0.HNm.local_norm [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (y : L) (hy : y ≠ 0) :
    (OverR R F L p).Finite ∧ ∃ a s : R, a ∉ p ∧ s ∉ p ∧
      Algebra.norm F y * algebraMap R F s = algebraMap R F g ^
        (∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ OverR R F L p),
          (fz F w : ℤ) * WithTop.untopD 0 (w y)) * algebraMap R F a := by sorry
