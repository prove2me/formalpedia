-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCompact_unitSpheres_3229e8b4fb16
-- name    : P2M_GroundTheory_Heights__Heights_isCompact_unitSpheres_3229e8b4fb16
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:46:44.260328+00:00
-- url     : https://prove2.me/theorems/e1021b62-3bec-5060-aa87-30bfce3d148a
-- title:
--   P2 M Ground Theory Heights  Heights is Compact unit Spheres 3229e8b4fb16: P2 M Ground Theory Heights  Heights is Compact unit Spheres 3229e8b4fb16
-- statement:
--   The P2 M Ground Theory Heights  Heights is Compact unit Spheres 3229e8b4fb16 construction uses the P2 M Ground Theory Heights  Heights is Compact unit Spheres 3229e8b4fb16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L42-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_isCompact_unitSpheres_3229e8b4fb16 : IsCompact (unitSpheres n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isCompact_unitSpheres» := P2M_GroundTheory_Heights__Heights_isCompact_unitSpheres_3229e8b4fb16
