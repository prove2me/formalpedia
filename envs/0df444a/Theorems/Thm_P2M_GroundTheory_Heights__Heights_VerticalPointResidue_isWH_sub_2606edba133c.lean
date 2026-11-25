-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_sub_2606edba133c
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_sub_2606edba133c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:26.186205+00:00
-- url     : https://prove2.me/theorems/c897a14e-0bb6-45a6-bb0b-95f2b9483432
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Residue is WH sub 2606edba133c: P2 M Ground Theory Heights  Heights Vertical Point Residue is WH sub 2606edba133c
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Residue is WH sub 2606edba133c construction uses the P2 M Ground Theory Heights  Heights Vertical Point Residue is WH sub 2606edba133c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L50-L56

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
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_sub_2606edba133c {f g : MRing (fun _ : Unit => T)} {n : ℕ}
    (hf : IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) f n)
    (hg : IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) g n) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) (f - g) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointResidue».«isWH_sub» := P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_sub_2606edba133c
