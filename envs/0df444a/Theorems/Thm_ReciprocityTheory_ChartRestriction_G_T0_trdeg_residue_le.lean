-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trdeg_residue_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.trdeg_residue_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:10.869183+00:00
-- url     : https://prove2.me/theorems/4e84d45b-5362-5b19-88b7-51c6f8897a1f
-- title:
--   T0: trdeg residue le
-- statement:
--   The T0 construction uses the trdeg residue le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L34-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L34-L176

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
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

theorem ReciprocityTheory.ChartRestriction.G.T0.trdeg_residue_le {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D : ℕ)
    (hD : Algebra.trdeg K Ω = D) (v : AddValuation Ω (WithTop ℤ))
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = 0) (a0 : Ω) (ha0 : a0 ≠ 0) (hva0 : v a0 ≠ 0) :
    letI := resAlg (F := K) v
    Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (vRing v)) ≤ ((D - 1 : ℕ) : Cardinal) := by sorry
