-- Prove2me | Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_hw_le_two_mul_b__ce7bc3374f49
-- name    : P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_hw_le_two_mul_b__ce7bc3374f49
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:12.039049+00:00
-- url     : https://prove2.me/theorems/f3809df6-f34a-4089-8d37-c812a644e9ba
-- title:
--   P2 M Formalism Cohomological Descent Log Small Constant Bounds hw le two mul b  ce7bc3374f49: P2 M Formalism Cohomological Descent Log Small Constant Bounds hw le two mul b  ce7bc3374f49
-- statement:
--   The P2 M Formalism Cohomological Descent Log Small Constant Bounds hw le two mul b  ce7bc3374f49 construction uses the P2 M Formalism Cohomological Descent Log Small Constant Bounds hw le two mul b  ce7bc3374f49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L539-L548
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L539-L548

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical

theorem P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_hw_le_two_mul_b__ce7bc3374f49 {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι} (hW : D.Widths P)
    {τ : ι} (hτ : τ ∉ D.T2) : D.hw τ ≤ 2 * P.b' := by sorry

alias «Formalism».«CohomologicalDescent».«LogSmallConstantBounds».«hw_le_two_mul_b'» := P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_hw_le_two_mul_b__ce7bc3374f49
