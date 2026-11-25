-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointNagata_comp_mem_69b2299180fb
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointNagata_comp_mem_69b2299180fb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:27.152537+00:00
-- url     : https://prove2.me/theorems/31f66bfe-f90e-5a82-9555-9130568f1846
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Nagata comp mem 69b2299180fb: P2 M Ground Theory Heights  Heights Vertical Point Nagata comp mem 69b2299180fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Nagata comp mem 69b2299180fb construction uses the P2 M Ground Theory Heights  Heights Vertical Point Nagata comp mem 69b2299180fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L31-L33

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointNagata_comp_mem_69b2299180fb {J : Ideal (MRing (fun _ : Unit => T))} (hJ : IsMultiHomogIdeal J)
    {f : MRing (fun _ : Unit => T)} (hf : f ∈ J) (n : ℕ) : comp n f ∈ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointNagata».«comp_mem» := P2M_GroundTheory_Heights__Heights_VerticalPointNagata_comp_mem_69b2299180fb
