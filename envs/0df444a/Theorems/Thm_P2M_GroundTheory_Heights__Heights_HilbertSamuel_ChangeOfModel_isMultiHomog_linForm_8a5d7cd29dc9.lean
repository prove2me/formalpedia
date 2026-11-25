-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChangeOfModel_isMultiHomog_linForm_8a5d7cd29dc9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChangeOfModel_isMultiHomog_linForm_8a5d7cd29dc9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:22:07.621815+00:00
-- url     : https://prove2.me/theorems/56d81c14-8d2e-5ead-ad35-f4522455abef
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Change Of Model is Multi Homog lin Form 8a5d7cd29dc9: P2 M Ground Theory Heights  Heights Hilbert Samuel Change Of Model is Multi Homog lin Form 8a5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Change Of Model is Multi Homog lin Form 8a5d7cd29dc9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Change Of Model is Multi Homog lin Form 8a5d7cd29dc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PChangeOfModel.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PChangeOfModel.lean#L25-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfModel
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
omit [Fintype K] [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChangeOfModel_isMultiHomog_linForm_8a5d7cd29dc9 (A : ∀ k, ι₂ k → ι k → ℤ) (q : Σ k, ι₂ k) :
    IsMultiHomog (linForm A q) (blockDeg q.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ChangeOfModel».«isMultiHomog_linForm» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChangeOfModel_isMultiHomog_linForm_8a5d7cd29dc9
