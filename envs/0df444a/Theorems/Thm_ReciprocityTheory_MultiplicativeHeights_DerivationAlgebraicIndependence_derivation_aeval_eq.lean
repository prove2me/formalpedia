-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_derivation_aeval_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:29.083262+00:00
-- url     : https://prove2.me/theorems/788fce01-c4c6-4705-9809-2a3882e3d0a1
-- title:
--   Derivation Algebraic Independence: derivation aeval eq
-- statement:
--   The Derivation Algebraic Independence construction uses the derivation aeval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AlgebraicIndependentOfDerivations.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AlgebraicIndependentOfDerivations.lean#L9-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    (d : Derivation K R R) (z : ι → R) (P : MvPolynomial ι K) :
    d (aeval z P) = ∑ i, aeval z (pderiv i P) * d (z i) := by sorry
