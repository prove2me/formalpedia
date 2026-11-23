-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_algebraicIndependent_of_residue_lift
-- name    : ReciprocityTheory.MultiplicativeHeights.algebraicIndependent_of_residue_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:04.792925+00:00
-- url     : https://prove2.me/theorems/809cfbe5-ac61-4402-a8eb-bf0b7673349d
-- title:
--   Multiplicative Heights: algebraic Independent of residue lift
-- statement:
--   The Multiplicative Heights construction uses the algebraic Independent of residue lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntegralClosureRankAndResidueTrdegLe.lean#L56-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntegralClosureRankAndResidueTrdegLe.lean#L56-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.algebraicIndependent_of_residue_lift {F₁ F₂ : Type} [Field F₁] [Field F₂] [Algebra F₁ F₂]
    (V : ValuationSubring F₂) {ι : Type*} (y : ι → V)
    (hx : letI := residueAlgebra V (algebraMap F₁ F₂)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (fun i => IsLocalRing.residue V (y i))) :
    AlgebraicIndependent F₁ (fun i => ((y i : V) : F₂)) := by sorry
