-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trdeg_eq_of_card
-- name    : ReciprocityTheory.ChartRestriction.G.T0.trdeg_eq_of_card
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:33.299503+00:00
-- url     : https://prove2.me/theorems/9d6d8571-acfb-4484-89d5-50a5b07e94ca
-- title:
--   T0: trdeg eq of card
-- statement:
--   The T0 construction uses the trdeg eq of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L178-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L178-L202

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

theorem ReciprocityTheory.ChartRestriction.G.T0.trdeg_eq_of_card {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] {σ τ : Type} [Fintype σ] [Fintype τ] (tb : σ → C)
    (ub : τ → C) (hu : AlgebraicIndependent F ub)
    (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) (n : ℕ)
    (hE : Algebra.trdeg F E ≤ n) (hcard : Fintype.card τ = Fintype.card σ + n)
    (hT : ∀ x : F, algebraMap F C x = algebraMap E C (algebraMap F E x)) :
    Algebra.trdeg F E = n ∧ AlgebraicIndependent E tb := by sorry
