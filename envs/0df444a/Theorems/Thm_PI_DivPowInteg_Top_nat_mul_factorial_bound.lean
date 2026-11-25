-- Prove2me | Theorems.Thm_PI_DivPowInteg_Top_nat_mul_factorial_bound
-- name    : PI.DivPowInteg.Top.nat_mul_factorial_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:27:15.448539+00:00
-- url     : https://prove2.me/theorems/38655461-5168-5a24-b030-6a856884d002
-- title:
--   Top: nat mul factorial bound
-- statement:
--   The Top construction uses the nat mul factorial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean#L33-L39

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

theorem PI.DivPowInteg.Top.nat_mul_factorial_bound (k : ℕ) :
    ((k + 1).factorial : ℚ)⁻¹ * ((k + 1 : ℕ) : ℚ) = (k.factorial : ℚ)⁻¹ := by sorry
