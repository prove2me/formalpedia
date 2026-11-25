-- Prove2me | Theorems.Thm_PI_DivPowInteg_Top_divPowInteg_of
-- name    : PI.DivPowInteg.Top.divPowInteg_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:27:25.592202+00:00
-- url     : https://prove2.me/theorems/274cf135-7995-58a4-a24a-d0e896a82695
-- title:
--   Top: div Pow Integ of
-- statement:
--   The Top construction uses the div Pow Integ of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean#L145-L152

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

theorem PI.DivPowInteg.Top.divPowInteg_of (h1 : PowXL) (h2 : PowXR) (h3 : VanL) (h4 : VanR) : PI.DivPowInteg := by sorry
