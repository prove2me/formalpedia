-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_levi_flagTerm_b4f9f88ef559
-- name    : P2M_GroundTheory_Heights__Heights_FourB_levi_flagTerm_b4f9f88ef559
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:37.879367+00:00
-- url     : https://prove2.me/theorems/634a4d61-ad5c-415a-82e4-319c223393ed
-- title:
--   P2 M Ground Theory Heights  Heights Four B levi flag Term b4f9f88ef559: P2 M Ground Theory Heights  Heights Four B levi flag Term b4f9f88ef559
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B levi flag Term b4f9f88ef559 construction uses the P2 M Ground Theory Heights  Heights Four B levi flag Term b4f9f88ef559 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L51-L64

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

theorem P2M_GroundTheory_Heights__Heights_FourB_levi_flagTerm_b4f9f88ef559 (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N)
    (w : (Σ _ : Fin f, LowerPair N) → ℂ) :
    levi (flagTerm f N p lam j) 0 w = if h : j.2.val + 1 < N then
      (lam j.1 j.2 - lam j.1 ⟨j.2.val + 1, h⟩) * tailSum p (j.2.val + 1)
        (lowerMatrix fun q => w ⟨j.1, q⟩) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«levi_flagTerm» := P2M_GroundTheory_Heights__Heights_FourB_levi_flagTerm_b4f9f88ef559
