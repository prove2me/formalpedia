-- Prove2me | Theorems.Thm_P2M_Formalism_CohomologicalDescent_ShortWeightBounds_weight_nonneg__27470cb891f0
-- name    : P2M_Formalism_CohomologicalDescent_ShortWeightBounds_weight_nonneg__27470cb891f0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:08.421798+00:00
-- url     : https://prove2.me/theorems/e6736cd7-3b3f-429b-992b-7d13e671acec
-- title:
--   P2 M Formalism Cohomological Descent Short Weight Bounds weight nonneg  27470cb891f0: P2 M Formalism Cohomological Descent Short Weight Bounds weight nonneg  27470cb891f0
-- statement:
--   The P2 M Formalism Cohomological Descent Short Weight Bounds weight nonneg  27470cb891f0 construction uses the P2 M Formalism Cohomological Descent Short Weight Bounds weight nonneg  27470cb891f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L182-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L182-L185

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds

theorem P2M_Formalism_CohomologicalDescent_ShortWeightBounds_weight_nonneg__27470cb891f0 (P : Par) {ι : Type} (W : Wts ι) (τ : ι) (a : ℕ) (h : a < P.Nr) :
    0 ≤ W.U P τ a := by sorry

alias «Formalism».«CohomologicalDescent».«ShortWeightBounds».«weight_nonneg'» := P2M_Formalism_CohomologicalDescent_ShortWeightBounds_weight_nonneg__27470cb891f0
