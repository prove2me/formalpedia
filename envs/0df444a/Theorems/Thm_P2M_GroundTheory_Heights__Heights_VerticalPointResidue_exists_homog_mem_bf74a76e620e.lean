-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_mem_bf74a76e620e
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_mem_bf74a76e620e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:50.504778+00:00
-- url     : https://prove2.me/theorems/cfd7611d-8594-4c29-8bb6-51ad358acc3d
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Residue exists homog mem bf74a76e620e: P2 M Ground Theory Heights  Heights Vertical Point Residue exists homog mem bf74a76e620e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Residue exists homog mem bf74a76e620e construction uses the P2 M Ground Theory Heights  Heights Vertical Point Residue exists homog mem bf74a76e620e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L77-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L77-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointResidue
variable {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_mem_bf74a76e620e {S : Type*} [CommRing S] (χ : MRing (fun _ : Unit => T) →+* S) (c : T)
    (hχ : χ (X ⟨(), c⟩) = 1) {W : Ideal (MRing (fun _ : Unit => T))} (hW : IsMultiHomogIdeal W)
    {f : MRing (fun _ : Unit => T)} (hf : f ∈ W) :
    ∃ (n : ℕ) (G : MRing (fun _ : Unit => T)), G ∈ W ∧ IsMultiHomog G (fun _ => n) ∧ χ G = χ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointResidue».«exists_homog_mem» := P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_mem_bf74a76e620e
