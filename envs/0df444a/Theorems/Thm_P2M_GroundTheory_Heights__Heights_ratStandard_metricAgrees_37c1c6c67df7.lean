-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratStandard_metricAgrees_37c1c6c67df7
-- name    : P2M_GroundTheory_Heights__Heights_ratStandard_metricAgrees_37c1c6c67df7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:00.745465+00:00
-- url     : https://prove2.me/theorems/53fd9a59-1e59-4cec-b347-e2ce9916c04e
-- title:
--   P2 M Ground Theory Heights  Heights rat Standard metric Agrees 37c1c6c67df7: P2 M Ground Theory Heights  Heights rat Standard metric Agrees 37c1c6c67df7
-- statement:
--   The P2 M Ground Theory Heights  Heights rat Standard metric Agrees 37c1c6c67df7 construction uses the P2 M Ground Theory Heights  Heights rat Standard metric Agrees 37c1c6c67df7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L227-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L227-L243

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
open Matrix

theorem P2M_GroundTheory_Heights__Heights_ratStandard_metricAgrees_37c1c6c67df7 (r : ℕ) :
    OneBlockMetricAgrees ratIntegerBasis (HermLattice.standard ℚ (r + 1))
      (HermLine.standard (oneBlockSizes 0 r)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ratStandard_metricAgrees» := P2M_GroundTheory_Heights__Heights_ratStandard_metricAgrees_37c1c6c67df7
