-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_logHeight_div_multihomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.T0.logHeight_div_multihomogeneous
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:48:41.257525+00:00
-- url     : https://prove2.me/theorems/37d7d538-8b15-5745-a1f3-6db9cbc7022e
-- title:
--   T0: log Height div multihomogeneous
-- statement:
--   The T0 construction uses the log Height div multihomogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightDivMultihomogeneous.lean#L40-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightDivMultihomogeneous.lean#L40-L76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightDivMultihomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.logHeight_div_multihomogeneous {B n : ℕ} {P Q R : MvPolynomial (Fin B × Fin n) K}
    (eQ eR : Fin B → ℕ) (hP : P ≠ 0) (hQ : Q ≠ 0) (hQm : IsMultiHomogeneous eQ Q)
    (hRm : IsMultiHomogeneous eR R) (hPQ : P * Q = R) :
    h0 P = h0 R - h0 Q := by sorry
