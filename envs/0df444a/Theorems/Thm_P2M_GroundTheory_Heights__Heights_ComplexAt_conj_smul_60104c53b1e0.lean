-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_conj_smul_60104c53b1e0
-- name    : P2M_GroundTheory_Heights__Heights_ComplexAt_conj_smul_60104c53b1e0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:56.882803+00:00
-- url     : https://prove2.me/theorems/a402a97e-bab0-5fee-930c-07a052f9dd56
-- title:
--   P2 M Ground Theory Heights  Heights Complex At conj smul 60104c53b1e0: P2 M Ground Theory Heights  Heights Complex At conj smul 60104c53b1e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex At conj smul 60104c53b1e0 construction uses the P2 M Ground Theory Heights  Heights Complex At conj smul 60104c53b1e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L52-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexAt
variable {K : Type*} {_ : Field K} (σ : K →+* ℂ)

theorem P2M_GroundTheory_Heights__Heights_ComplexAt_conj_smul_60104c53b1e0 (c : ℂ) (z : ComplexAt σ) : conj σ (c • z) = starRingEnd ℂ c • conj σ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexAt».«conj_smul» := P2M_GroundTheory_Heights__Heights_ComplexAt_conj_smul_60104c53b1e0
