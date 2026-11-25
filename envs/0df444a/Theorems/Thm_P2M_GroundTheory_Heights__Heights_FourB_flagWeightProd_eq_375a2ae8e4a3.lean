-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_flagWeightProd_eq_375a2ae8e4a3
-- name    : P2M_GroundTheory_Heights__Heights_FourB_flagWeightProd_eq_375a2ae8e4a3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:31.079989+00:00
-- url     : https://prove2.me/theorems/97ef1581-2abe-4479-bca3-d3a7cc91a24e
-- title:
--   P2 M Ground Theory Heights  Heights Four B flag Weight Prod eq 375a2ae8e4a3: P2 M Ground Theory Heights  Heights Four B flag Weight Prod eq 375a2ae8e4a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B flag Weight Prod eq 375a2ae8e4a3 construction uses the P2 M Ground Theory Heights  Heights Four B flag Weight Prod eq 375a2ae8e4a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FourB_flagWeightProd_eq_375a2ae8e4a3 (f N p : ℕ) (lam : Fin f → Fin N → ℝ) :
    flagWeightProd f N p lam = fun z => ∑ j : Fin f × Fin N, flagTerm f N p lam j z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«flagWeightProd_eq» := P2M_GroundTheory_Heights__Heights_FourB_flagWeightProd_eq_375a2ae8e4a3
