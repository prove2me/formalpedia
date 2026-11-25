-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_nbMain
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Nb.nbMain
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:45.162297+00:00
-- url     : https://prove2.me/theorems/a96b1227-e51b-4f56-8324-65c11ad45a26
-- title:
--   Nb: nb Main
-- statement:
--   The Nb construction uses the nb Main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/IsPrecompleteOfBasis.lean#L203-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/IsPrecompleteOfBasis.lean#L203-L284

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Nb.nbMain (n : ℕ) : ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [IsAdicComplete (maximalIdeal V') V']
    (k'' : Type) [Field k''] [Algebra (ResidueField V') k'']
    [FiniteDimensional (ResidueField V') k''], Module.finrank (ResidueField V') k'' = n →
    ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
      (_ : IsAdicComplete (maximalIdeal V'') V'') (_ : Algebra V' V''),
      Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧
      ∃ (_ : IsLocalHom (algebraMap V' V'')) (e : k'' ≃+* ResidueField V''),
        e.toRingHom.comp (algebraMap (ResidueField V') k'') =
          ResidueField.map (algebraMap V' V'') := by sorry
