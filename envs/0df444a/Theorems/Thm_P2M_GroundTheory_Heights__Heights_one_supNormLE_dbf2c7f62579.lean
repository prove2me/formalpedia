-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_one_supNormLE_dbf2c7f62579
-- name    : P2M_GroundTheory_Heights__Heights_one_supNormLE_dbf2c7f62579
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:48.596962+00:00
-- url     : https://prove2.me/theorems/c1a4c4e5-6a8d-4ae8-bfae-616af052902b
-- title:
--   P2 M Ground Theory Heights  Heights one sup Norm LE dbf2c7f62579: P2 M Ground Theory Heights  Heights one sup Norm LE dbf2c7f62579
-- statement:
--   The P2 M Ground Theory Heights  Heights one sup Norm LE dbf2c7f62579 construction uses the P2 M Ground Theory Heights  Heights one sup Norm LE dbf2c7f62579 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L176-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L176-L191

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

theorem P2M_GroundTheory_Heights__Heights_one_supNormLE_dbf2c7f62579 :
    ((IntegralSection.one (ArithVariety.whole n)).cast (standard_quot_deg n)).SupNormLE
      (((HermLine.standard n).pow 1).mul (HermLine.standard n).inv) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«one_supNormLE» := P2M_GroundTheory_Heights__Heights_one_supNormLE_dbf2c7f62579
