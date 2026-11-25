-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_eq_eval__d8b4e12d492f
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_eq_eval__d8b4e12d492f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:26:37.031091+00:00
-- url     : https://prove2.me/theorems/ec68210a-449d-4578-a584-a0d9268979e3
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Nagata aeval eq eval  d8b4e12d492f: P2 M Ground Theory Heights  Heights Vertical Point Nagata aeval eq eval  d8b4e12d492f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Nagata aeval eq eval  d8b4e12d492f construction uses the P2 M Ground Theory Heights  Heights Vertical Point Nagata aeval eq eval  d8b4e12d492f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L37-L39

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_eq_eval__d8b4e12d492f {S : Type*} [CommRing S] [Algebra ℤ S] (v : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) : aeval v f = eval₂ (Int.castRingHom S) v f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointNagata».«aeval_eq_eval₂» := P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_eq_eval__d8b4e12d492f
