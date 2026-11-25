-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_schur_d5169a16bac0
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_schur_d5169a16bac0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:23.034808+00:00
-- url     : https://prove2.me/theorems/8047c5df-13ac-4072-921a-fa1829ffb705
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff schur d5169a16bac0: P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff schur d5169a16bac0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff schur d5169a16bac0 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff schur d5169a16bac0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L197-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L197-L219

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_schur_d5169a16bac0 (σ : Type*) [Fintype σ] [DecidableEq σ] {m : ℕ} (ν : Fin m → ℕ)
    (hν : Antitone ν) : constantCoeff (schur σ ν) = if ν = 0 then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«constantCoeff_schur» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_schur_d5169a16bac0
