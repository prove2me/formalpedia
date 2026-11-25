-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_46ce3eed0a97
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_46ce3eed0a97
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:18.027042+00:00
-- url     : https://prove2.me/theorems/de973a8f-69a1-5576-9fee-5a6e28f907af
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT diff Step 46ce3eed0a97: P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT diff Step 46ce3eed0a97
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT diff Step 46ce3eed0a97 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT diff Step 46ce3eed0a97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PModulesFromPrimes.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PModulesFromPrimes.lean#L16-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PModulesFromPrimes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTOfUnitSteps_degLT_diffStep_f67a5cef2aae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_46ce3eed0a97 {K : Type*} {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1))
    (b : K → ℤ) : DegLT (diffStep b f) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«degLT_diffStep» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_46ce3eed0a97
