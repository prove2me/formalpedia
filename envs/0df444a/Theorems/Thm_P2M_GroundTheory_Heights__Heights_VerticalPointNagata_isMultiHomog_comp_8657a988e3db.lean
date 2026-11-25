-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointNagata_isMultiHomog_comp_8657a988e3db
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointNagata_isMultiHomog_comp_8657a988e3db
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:25.574805+00:00
-- url     : https://prove2.me/theorems/ca39c3ef-3a9c-5efc-81ce-a84aa141e474
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Nagata is Multi Homog comp 8657a988e3db: P2 M Ground Theory Heights  Heights Vertical Point Nagata is Multi Homog comp 8657a988e3db
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Nagata is Multi Homog comp 8657a988e3db construction uses the P2 M Ground Theory Heights  Heights Vertical Point Nagata is Multi Homog comp 8657a988e3db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L20-L22

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointNagata_isMultiHomog_comp_8657a988e3db (n : ℕ) (f : MRing (fun _ : Unit => T)) :
    IsMultiHomog (comp n f) (fun _ => n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointNagata».«isMultiHomog_comp» := P2M_GroundTheory_Heights__Heights_VerticalPointNagata_isMultiHomog_comp_8657a988e3db
