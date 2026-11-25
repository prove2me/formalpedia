-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockAddData_extMap_8a459cfaa920
-- name    : P2M_GroundTheory_Heights__Heights_blockAddData_extMap_8a459cfaa920
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:13.749843+00:00
-- url     : https://prove2.me/theorems/33909f48-4534-48b2-bc40-b942a56c5987
-- title:
--   P2 M Ground Theory Heights  Heights block Add Data ext Map 8a459cfaa920: P2 M Ground Theory Heights  Heights block Add Data ext Map 8a459cfaa920
-- statement:
--   The P2 M Ground Theory Heights  Heights block Add Data ext Map 8a459cfaa920 construction uses the P2 M Ground Theory Heights  Heights block Add Data ext Map 8a459cfaa920 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L112-L117

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
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_blockAddData_extMap_8a459cfaa920 :
    (blockAddData n k₀).extMap = (MvPolynomial.map (ArithVariety.whole n).mkF).comp (blockSubst n k₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockAddData_extMap» := P2M_GroundTheory_Heights__Heights_blockAddData_extMap_8a459cfaa920
