-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_algebraicIndependent_residue_of_isUnit
-- name    : ReciprocityTheory.ChartRestriction.G.T0.algebraicIndependent_residue_of_isUnit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:24.978705+00:00
-- url     : https://prove2.me/theorems/5670025d-0882-44b8-9917-abac43d3b737
-- title:
--   T0: algebraic Independent residue of is Unit
-- statement:
--   The T0 construction uses the algebraic Independent residue of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L15-L32

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

theorem ReciprocityTheory.ChartRestriction.G.T0.algebraicIndependent_residue_of_isUnit {A R E : Type} [CommRing A] [Field R] [Field E] (V : ValuationSubring E)
    [Algebra R (IsLocalRing.ResidueField V)] (φ : A →+* V) (ψ : A →+* R)
    (hψ : Function.Surjective ψ)
    (hc : ∀ a, algebraMap R (IsLocalRing.ResidueField V) (ψ a) = IsLocalRing.residue V (φ a))
    {τ : Type} (t : τ → V) (h : ∀ q : MvPolynomial τ A, q.map ψ ≠ 0 → IsUnit (eval₂ φ t q)) :
    AlgebraicIndependent R (fun j => IsLocalRing.residue V (t j)) := by sorry
