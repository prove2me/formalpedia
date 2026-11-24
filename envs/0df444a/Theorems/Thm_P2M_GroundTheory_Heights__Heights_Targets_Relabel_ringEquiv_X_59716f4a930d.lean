-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_X_59716f4a930d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_X_59716f4a930d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:23.534298+00:00
-- url     : https://prove2.me/theorems/545f7b95-acc5-4bc8-890b-c2f96b399c8e
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel ring Equiv X 59716f4a930d: P2 M Ground Theory Heights  Heights Targets Relabel ring Equiv X 59716f4a930d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel ring Equiv X 59716f4a930d construction uses the P2 M Ground Theory Heights  Heights Targets Relabel ring Equiv X 59716f4a930d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L52-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_X_59716f4a930d (k : K) (i : ι k) :
    ringEquiv F e h (X ⟨k, i⟩) = X ⟨e k, h k i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«ringEquiv_X» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_X_59716f4a930d
