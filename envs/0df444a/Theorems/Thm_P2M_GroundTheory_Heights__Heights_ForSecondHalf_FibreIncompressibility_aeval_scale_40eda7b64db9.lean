-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_aeval_scale_40eda7b64db9
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_aeval_scale_40eda7b64db9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:41:41.912798+00:00
-- url     : https://prove2.me/theorems/aeabbdf7-2eb2-5485-93dc-cf16de71368d
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility aeval scale 40eda7b64db9: P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility aeval scale 40eda7b64d
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility aeval scale 40eda7b64db9 construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility aeval scale 40eda7b64db9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncompTrdeg.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncompTrdeg.lean#L17-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncompTrdeg
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
variable {S : Type} [CommRing S]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_aeval_scale_40eda7b64db9 {A : Type} [CommRing A] [Algebra S A] {g : MRingOver S ι'} {a : K' → ℕ}
    (hg : IsMultiHomog g a) (c : K' → A) (z : (Σ k, ι' k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ a k) * aeval z g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreIncompressibility».«aeval_scale» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_aeval_scale_40eda7b64db9
