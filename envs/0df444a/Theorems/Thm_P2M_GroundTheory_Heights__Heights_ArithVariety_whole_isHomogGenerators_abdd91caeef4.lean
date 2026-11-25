-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isHomogGenerators_abdd91caeef4
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isHomogGenerators_abdd91caeef4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:08:06.043627+00:00
-- url     : https://prove2.me/theorems/c53ae2dc-cc83-4d61-a470-dde368ceeca7
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety whole is Homog Generators abdd91caeef4: P2 M Ground Theory Heights  Heights Arith Variety whole is Homog Generators abdd91caeef4
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety whole is Homog Generators abdd91caeef4 construction uses the P2 M Ground Theory Heights  Heights Arith Variety whole is Homog Generators abdd91caeef4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L43-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.ArithVariety
variable (n : ι → ℕ)
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isHomogGenerators_abdd91caeef4 :
    (whole n).IsHomogGenerators (fun i : Fin 0 ↦ i.elim0) (fun i : Fin 0 ↦ i.elim0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«whole_isHomogGenerators» := P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isHomogGenerators_abdd91caeef4
