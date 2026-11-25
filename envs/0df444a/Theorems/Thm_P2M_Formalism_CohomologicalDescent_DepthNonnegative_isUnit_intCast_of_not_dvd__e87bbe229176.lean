-- Prove2me | Theorems.Thm_P2M_Formalism_CohomologicalDescent_DepthNonnegative_isUnit_intCast_of_not_dvd__e87bbe229176
-- name    : P2M_Formalism_CohomologicalDescent_DepthNonnegative_isUnit_intCast_of_not_dvd__e87bbe229176
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:46.323878+00:00
-- url     : https://prove2.me/theorems/6e1b80ec-0602-4ffc-a60b-b032711e1cd7
-- title:
--   P2 M Formalism Cohomological Descent Depth Nonnegative is Unit int Cast of not dvd  e87bbe229176: P2 M Formalism Cohomological Descent Depth Nonnegative is Unit int Cast of not dvd  e87bbe229176
-- statement:
--   The P2 M Formalism Cohomological Descent Depth Nonnegative is Unit int Cast of not dvd  e87bbe229176 construction uses the P2 M Formalism Cohomological Descent Depth Nonnegative is Unit int Cast of not dvd  e87bbe229176 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L18-L32

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

theorem P2M_Formalism_CohomologicalDescent_DepthNonnegative_isUnit_intCast_of_not_dvd__e87bbe229176 (R : Type) [CommRing R] (l : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : IsUnit (m : R) := by sorry

alias «Formalism».«CohomologicalDescent».«DepthNonnegative».«isUnit_intCast_of_not_dvd'» := P2M_Formalism_CohomologicalDescent_DepthNonnegative_isUnit_intCast_of_not_dvd__e87bbe229176
