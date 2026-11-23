-- Prove2me | Theorems.Thm_PI_DivPowInteg_Gen_gdelta_pow_succ_apply
-- name    : PI.DivPowInteg.Gen.gdelta_pow_succ_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:07.540547+00:00
-- url     : https://prove2.me/theorems/f04a7f94-a3c0-487f-8ba2-6da5c9635a16
-- title:
--   Gen: gdelta pow succ apply
-- statement:
--   The Gen construction uses the gdelta pow succ apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenPow.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenPow.lean#L69-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem PI.DivPowInteg.Gen.gdelta_pow_succ_apply (κ : I → J → K) (m : ℕ) (S : MvPolynomial (I ⊕ J) K) :
    (gdelta κ ^ (m + 1)) S = gdelta κ ((gdelta κ ^ m) S) := by sorry
