-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_isMaximalCompact_maxCompact_361840dcefd4
-- name    : P2M_GroundTheory_Heights__Theta_isMaximalCompact_maxCompact_361840dcefd4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:33.990869+00:00
-- url     : https://prove2.me/theorems/59e95330-dd8f-5a6b-b53e-42fefcd76ffe
-- title:
--   P2 M Ground Theory Heights  Theta is Maximal Compact max Compact 361840dcefd4: P2 M Ground Theory Heights  Theta is Maximal Compact max Compact 361840dcefd4
-- statement:
--   The P2 M Ground Theory Heights  Theta is Maximal Compact max Compact 361840dcefd4 construction uses the P2 M Ground Theory Heights  Theta is Maximal Compact max Compact 361840dcefd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L249-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L249-L252

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

theorem P2M_GroundTheory_Heights__Theta_isMaximalCompact_maxCompact_361840dcefd4 :
    IsCompact ((maxCompact G : Subgroup G) : Set G) ∧
      ∀ L : Subgroup G, IsCompact (L : Set G) → maxCompact G ≤ L → L = maxCompact G := by sorry

alias «GroundTheory».«Heights₂».«Theta».«isMaximalCompact_maxCompact» := P2M_GroundTheory_Heights__Theta_isMaximalCompact_maxCompact_361840dcefd4
