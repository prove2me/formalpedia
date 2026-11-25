-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratDoubled_latticeMetricAgrees_68e856580721
-- name    : P2M_GroundTheory_Heights__Heights_ratDoubled_latticeMetricAgrees_68e856580721
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:16.839552+00:00
-- url     : https://prove2.me/theorems/0901d374-dd70-5983-a51f-f05aa585f71c
-- title:
--   P2 M Ground Theory Heights  Heights rat Doubled lattice Metric Agrees 68e856580721: P2 M Ground Theory Heights  Heights rat Doubled lattice Metric Agrees 68e856580721
-- statement:
--   The P2 M Ground Theory Heights  Heights rat Doubled lattice Metric Agrees 68e856580721 construction uses the P2 M Ground Theory Heights  Heights rat Doubled lattice Metric Agrees 68e856580721 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L186-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L186-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel
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
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_ratDoubled_latticeMetricAgrees_68e856580721 (r : ℕ) :
    LatticeMetricAgrees (fun j : Fin (r + 1) ↦ (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ))
      (ratDoubled r) ((HermLine.standard (fun _ : Unit ↦ r)).scale 2 two_pos) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ratDoubled_latticeMetricAgrees» := P2M_GroundTheory_Heights__Heights_ratDoubled_latticeMetricAgrees_68e856580721
