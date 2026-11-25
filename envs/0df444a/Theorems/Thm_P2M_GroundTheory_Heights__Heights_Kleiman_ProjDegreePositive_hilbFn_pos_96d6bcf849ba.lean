-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_hilbFn_pos_96d6bcf849ba
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_hilbFn_pos_96d6bcf849ba
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:58:27.285316+00:00
-- url     : https://prove2.me/theorems/9ba68211-e541-4b70-a65b-57a1d3610179
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive hilb Fn pos 96d6bcf849ba: P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive hilb Fn pos 96d6bcf849ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive hilb Fn pos 96d6bcf849ba construction uses the P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive hilb Fn pos 96d6bcf849ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L104-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L104-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegreePos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PProjDegreePositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.ProjDegreePositive
variable {F : Type u} [Field F] {ι₀ : Type} [Fintype ι₀]
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_hilbFn_pos_96d6bcf849ba (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) (n : ℕ) :
    0 < hilbFn q (fun _ => (n : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ProjDegreePositive».«hilbFn_pos» := P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_hilbFn_pos_96d6bcf849ba
