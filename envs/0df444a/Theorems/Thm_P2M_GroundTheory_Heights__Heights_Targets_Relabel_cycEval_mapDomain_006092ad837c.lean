-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_cycEval_mapDomain_006092ad837c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_cycEval_mapDomain_006092ad837c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:46.523519+00:00
-- url     : https://prove2.me/theorems/ef10cbf9-3d45-4f40-ba53-e29e8d211116
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel cyc Eval map Domain 006092ad837c: P2 M Ground Theory Heights  Heights Targets Relabel cyc Eval map Domain 006092ad837c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel cyc Eval map Domain 006092ad837c construction uses the P2 M Ground Theory Heights  Heights Targets Relabel cyc Eval map Domain 006092ad837c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L31-L35

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

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_cycEval_mapDomain_006092ad837c (c : Ideal (MRingOver F ι) → Ideal (MRingOver F ι'))
    (N : Ideal (MRingOver F ι') → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval N (Finsupp.mapDomain c D) = cycEval (fun W => N (c W)) D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«cycEval_mapDomain» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_cycEval_mapDomain_006092ad837c
