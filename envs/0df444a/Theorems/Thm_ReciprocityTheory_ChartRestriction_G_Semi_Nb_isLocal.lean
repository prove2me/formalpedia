-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_isLocal
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Nb.isLocal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:26:05.164696+00:00
-- url     : https://prove2.me/theorems/e7e50bf1-7a5e-4538-b24e-1b7573aac31d
-- title:
--   Nb: is Local
-- statement:
--   The Nb construction uses the is Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/IsPrecompleteOfBasis.lean#L112-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/IsPrecompleteOfBasis.lean#L112-L121

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
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (f : V[X]) (hf : f.Monic) (hg : Irreducible (f.map (residue V)))
include hf hg

theorem ReciprocityTheory.ChartRestriction.G.Semi.Nb.isLocal : IsLocalRing (AdjoinRoot f) := by sorry
