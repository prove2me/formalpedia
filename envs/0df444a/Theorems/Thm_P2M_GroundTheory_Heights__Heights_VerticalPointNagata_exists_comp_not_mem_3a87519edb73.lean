-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointNagata_exists_comp_not_mem_3a87519edb73
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointNagata_exists_comp_not_mem_3a87519edb73
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:25.908335+00:00
-- url     : https://prove2.me/theorems/61133cd9-8ad9-4c82-bd82-754b8c38c0a2
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Nagata exists comp not mem 3a87519edb73: P2 M Ground Theory Heights  Heights Vertical Point Nagata exists comp not mem 3a87519edb73
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Nagata exists comp not mem 3a87519edb73 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Nagata exists comp not mem 3a87519edb73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
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
open GroundTheory.Heights₂.Heights.VerticalPointNagata
variable {T : Type} [Fintype T]
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_VerticalPointNagata_exists_comp_not_mem_3a87519edb73 {J : Ideal (MRing (fun _ : Unit => T))} {f : MRing (fun _ : Unit => T)}
    (hf : f ∉ J) : ∃ n, comp n f ∉ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointNagata».«exists_comp_not_mem» := P2M_GroundTheory_Heights__Heights_VerticalPointNagata_exists_comp_not_mem_3a87519edb73
