-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_det_subtype_comp_associated_prod
-- name    : ReciprocityTheory.MultiplicativeHeights.det_subtype_comp_associated_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:37.340014+00:00
-- url     : https://prove2.me/theorems/7397c3f9-eba2-4a5f-8a1a-834bbd2f98c5
-- title:
--   Multiplicative Heights: det subtype comp associated prod
-- statement:
--   The Multiplicative Heights construction uses the det subtype comp associated prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/DetSubtypeCompAssociatedProd.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/DetSubtypeCompAssociatedProd.lean#L10-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Lemmata_GeneralBFactLast_Imports
import Definitions.Def_Lemmata_GeneralBFactTail_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetSubtypeCompAssociatedProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module Submodule

theorem ReciprocityTheory.MultiplicativeHeights.det_subtype_comp_associated_prod {R M : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R M) (N : Submodule R M)
    (h : finrank R N = finrank R M) (e : M ≃ₗ[R] N) :
    Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N)))
      (∏ i, smithNormalFormCoeffs b h i) := by sorry
