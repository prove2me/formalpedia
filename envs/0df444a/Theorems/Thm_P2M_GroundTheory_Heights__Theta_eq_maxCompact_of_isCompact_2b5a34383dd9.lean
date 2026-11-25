-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_eq_maxCompact_of_isCompact_2b5a34383dd9
-- name    : P2M_GroundTheory_Heights__Theta_eq_maxCompact_of_isCompact_2b5a34383dd9
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:29.681776+00:00
-- url     : https://prove2.me/theorems/d8decc55-8825-559d-a494-5a51dfd53826
-- title:
--   P2 M Ground Theory Heights  Theta eq max Compact of is Compact 2b5a34383dd9: P2 M Ground Theory Heights  Theta eq max Compact of is Compact 2b5a34383dd9
-- statement:
--   The P2 M Ground Theory Heights  Theta eq max Compact of is Compact 2b5a34383dd9 construction uses the P2 M Ground Theory Heights  Theta eq max Compact of is Compact 2b5a34383dd9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L222-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L222-L247

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {p q : ℕ}
local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "J" => indefJ p q
local notation "G" => indefiniteUnitaryGroup p q

theorem P2M_GroundTheory_Heights__Theta_eq_maxCompact_of_isCompact_2b5a34383dd9 {L : Subgroup G} (hL : IsCompact (L : Set G))
    (hK : maxCompact G ≤ L) : L = maxCompact G := by sorry

alias «GroundTheory».«Heights₂».«Theta».«eq_maxCompact_of_isCompact» := P2M_GroundTheory_Heights__Theta_eq_maxCompact_of_isCompact_2b5a34383dd9
