-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_2fc2a6e46147
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_2fc2a6e46147
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:46.821095+00:00
-- url     : https://prove2.me/theorems/ea11df35-cc6e-4fdb-a742-bcd44c8ad0ea
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Residue exists homog 2fc2a6e46147: P2 M Ground Theory Heights  Heights Vertical Point Residue exists homog 2fc2a6e46147
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Residue exists homog 2fc2a6e46147 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Residue exists homog 2fc2a6e46147 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L58-L75

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_2fc2a6e46147 {S : Type*} [CommRing S] (χ : MRing (fun _ : Unit => T) →+* S) (c : T)
    (hχ : χ (X ⟨(), c⟩) = 1) (f : MRing (fun _ : Unit => T)) :
    ∃ (n : ℕ) (G : MRing (fun _ : Unit => T)), IsMultiHomog G (fun _ => n) ∧ χ G = χ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointResidue».«exists_homog» := P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_2fc2a6e46147
