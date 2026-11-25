-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HNm_fin_support
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HNm.fin_support
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:35.794477+00:00
-- url     : https://prove2.me/theorems/c830c166-fc35-4f2e-8d22-84eb134731de
-- title:
--   HNm: fin support
-- statement:
--   The HNm construction uses the fin support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormB.lean#L82-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormB.lean#L82-L120

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

theorem ReciprocityTheory.ChartRestriction.G.T0.HNm.fin_support [FiniteDimensional F L] (y : L) (hy : y ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ ∃ w ∈ OverR R F L p, w y ≠ 0}.Finite := by sorry
