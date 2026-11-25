-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_term_e0faee39c19e
-- name    : P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_term_e0faee39c19e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:16.754606+00:00
-- url     : https://prove2.me/theorems/4f7ff201-10ed-5cdd-a31c-106304f108f2
-- title:
--   P2 M Ground Theory Heights  Heights Four B deriv deriv term e0faee39c19e: P2 M Ground Theory Heights  Heights Four B deriv deriv term e0faee39c19e
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B deriv deriv term e0faee39c19e construction uses the P2 M Ground Theory Heights  Heights Four B deriv deriv term e0faee39c19e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L44-L49

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

theorem P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_term_e0faee39c19e {f N : ℕ} (p : ℕ) (c : ℝ) (i : ℕ) (hi : i ≤ N) (τ : Fin f)
    (v : (Σ _ : Fin f, LowerPair N) → ℂ) :
    deriv (deriv fun t : ℝ => c * flagPs N p i hi fun q => (t • v) ⟨τ, q⟩) 0 =
      c * (2 * tailSum p i (lowerMatrix fun q => v ⟨τ, q⟩)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«deriv_deriv_term» := P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_term_e0faee39c19e
