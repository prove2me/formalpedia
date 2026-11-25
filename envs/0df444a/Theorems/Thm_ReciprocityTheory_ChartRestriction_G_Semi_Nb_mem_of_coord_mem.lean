-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_mem_of_coord_mem
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Nb.mem_of_coord_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:08.534701+00:00
-- url     : https://prove2.me/theorems/0a01f246-5e9c-48ea-acc7-4acd5e83516d
-- title:
--   Nb: mem of coord mem
-- statement:
--   The Nb construction uses the mem of coord mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/IsPrecompleteOfBasis.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/IsPrecompleteOfBasis.lean#L33-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Tower
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open IsLocalRing Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Semi.Nb
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.Semi.Nb.mem_of_coord_mem (b : Module.Basis ι R M) (J : Ideal R) {x : M}
    (h : ∀ i, b.repr x i ∈ J) : x ∈ (J • ⊤ : Submodule R M) := by sorry
