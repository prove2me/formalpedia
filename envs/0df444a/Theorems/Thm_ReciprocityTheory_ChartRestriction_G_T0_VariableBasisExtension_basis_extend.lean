-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_VariableBasisExtension_basis_extend
-- name    : ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.basis_extend
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:13.101709+00:00
-- url     : https://prove2.me/theorems/fe9e02cd-a27d-42f2-9dd8-08205ec74872
-- title:
--   Variable Basis Extension: basis extend
-- statement:
--   The Variable Basis Extension construction uses the basis extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BasisExtend.lean#L15-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BasisExtend.lean#L15-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LinearIndependentC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension
variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.basis_extend [FiniteDimensional L E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n L E) :
    letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
      (liftY (L := L) (E := E) (σ := σ)).toAlgebra;
    ∃ b' : Module.Basis n (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)),
      (∀ i, b' i = algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.C (b i))) ∧
      ∀ e : E, Algebra.leftMulMatrix b' (algebraMap (MvPolynomial σ E)
          (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e)) =
        (Algebra.leftMulMatrix b e).map (algebraMap L (FractionRing (MvPolynomial σ L))) := by sorry
