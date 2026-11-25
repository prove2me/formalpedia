-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_primeWeight_le_f203a85ab173
-- name    : P2M_GroundTheory_Heights__Heights_Model_primeWeight_le_f203a85ab173
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:28.704564+00:00
-- url     : https://prove2.me/theorems/7482cbfc-2ad9-400e-9f81-261c04e5f92a
-- title:
--   P2 M Ground Theory Heights  Heights Model prime Weight le f203a85ab173: P2 M Ground Theory Heights  Heights Model prime Weight le f203a85ab173
-- statement:
--   The P2 M Ground Theory Heights  Heights Model prime Weight le f203a85ab173 construction uses the P2 M Ground Theory Heights  Heights Model prime Weight le f203a85ab173 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSumCp.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSumCp.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSumCp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model

theorem P2M_GroundTheory_Heights__Heights_Model_primeWeight_le_f203a85ab173 {p : ℕ} (hp : p.Prime) : primeWeight p ≤ 4 / p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«primeWeight_le» := P2M_GroundTheory_Heights__Heights_Model_primeWeight_le_f203a85ab173
