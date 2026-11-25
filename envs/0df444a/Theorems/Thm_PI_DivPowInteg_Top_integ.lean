-- Prove2me | Theorems.Thm_PI_DivPowInteg_Top_integ
-- name    : PI.DivPowInteg.Top.integ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:27:09.56093+00:00
-- url     : https://prove2.me/theorems/572ffa2b-7131-5c69-b97b-40cb8ab02151
-- title:
--   Top: integ
-- statement:
--   The Top construction uses the integ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean#L97-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean#L97-L141

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_NatMulFactorialBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Top
open PI.DivPowInteg.Gen
variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]

theorem PI.DivPowInteg.Top.integ (h1 : PowXL) (h2 : PowXR) (L : Submodule A K) (κ : I → J → K)
    (hκ : ∀ i j, κ i j ∈ L) (P : MvPolynomial (I ⊕ J) A) :
    ∀ n, Good L n (dpow κ n (map (algebraMap A K) P)) := by sorry
