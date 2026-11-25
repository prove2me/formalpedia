-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_snoc_comp_2c85a72d5335
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_snoc_comp_2c85a72d5335
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:29.26856+00:00
-- url     : https://prove2.me/theorems/c7f337e6-1790-4777-a2c6-431d22ecebac
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel snoc comp 2c85a72d5335: P2 M Ground Theory Heights  Heights Targets Relabel snoc comp 2c85a72d5335
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel snoc comp 2c85a72d5335 construction uses the P2 M Ground Theory Heights  Heights Targets Relabel snoc comp 2c85a72d5335 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L17-L23

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

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_snoc_comp_2c85a72d5335 {K₁ K₂ : Type*} (c : K₁ → K₂) {n : ℕ} (L : Fin n → K₂ → ℤ) (A : K₂ → ℤ) :
    (fun j => Fin.snoc (α := fun _ => K₂ → ℤ) L A j ∘ c) =
      Fin.snoc (α := fun _ => K₁ → ℤ) (fun j => L j ∘ c) (A ∘ c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«snoc_comp» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_snoc_comp_2c85a72d5335
