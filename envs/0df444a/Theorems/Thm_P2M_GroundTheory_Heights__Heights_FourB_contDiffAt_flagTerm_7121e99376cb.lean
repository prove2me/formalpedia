-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_contDiffAt_flagTerm_7121e99376cb
-- name    : P2M_GroundTheory_Heights__Heights_FourB_contDiffAt_flagTerm_7121e99376cb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:58.737451+00:00
-- url     : https://prove2.me/theorems/483a1a98-11bf-4bef-a564-d9cc55b3bd24
-- title:
--   P2 M Ground Theory Heights  Heights Four B cont Diff At flag Term 7121e99376cb: P2 M Ground Theory Heights  Heights Four B cont Diff At flag Term 7121e99376cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B cont Diff At flag Term 7121e99376cb construction uses the P2 M Ground Theory Heights  Heights Four B cont Diff At flag Term 7121e99376cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L27-L34

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

theorem P2M_GroundTheory_Heights__Heights_FourB_contDiffAt_flagTerm_7121e99376cb (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N) :
    ContDiffAt ℝ 2 (flagTerm f N p lam j) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«contDiffAt_flagTerm» := P2M_GroundTheory_Heights__Heights_FourB_contDiffAt_flagTerm_7121e99376cb
