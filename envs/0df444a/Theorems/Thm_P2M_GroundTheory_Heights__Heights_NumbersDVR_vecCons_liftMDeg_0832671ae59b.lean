-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vecCons_liftMDeg_0832671ae59b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_vecCons_liftMDeg_0832671ae59b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:53.403303+00:00
-- url     : https://prove2.me/theorems/a5cbf61e-3e8e-4abd-b2b9-db4046dc8749
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR vec Cons lift MDeg 0832671ae59b: P2 M Ground Theory Heights  Heights Numbers DVR vec Cons lift MDeg 0832671ae59b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR vec Cons lift MDeg 0832671ae59b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR vec Cons lift MDeg 0832671ae59b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L56-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_vecCons_liftMDeg_0832671ae59b {d : ℕ} (c : K → ℕ) (L : Fin d → K → ℤ) :
    Matrix.vecCons (fun k => ((liftMDeg c k : ℕ) : ℤ)) (liftDegs L) =
      liftDegs (Matrix.vecCons (fun k => (c k : ℤ)) L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«vecCons_liftMDeg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_vecCons_liftMDeg_0832671ae59b
