-- Prove2me | Theorems.Thm_PermanentRollout_permanent_rollout_minimalPrime_isHomogeneous
-- name    : PermanentRollout.permanent_rollout_minimalPrime_isHomogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/e78b107b-b08d-417b-b245-6478967787c2
-- title:
--   PermanentRollout.permanent_rollout_minimalPrime_isHomogeneous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section

theorem PermanentRollout.permanent_rollout_minimalPrime_isHomogeneous
    {ι σ R : Type*} [CommRing R]
    [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι]
    [SetLike σ R] [AddSubmonoidClass σ R]
    {𝒜 : ι → σ} [GradedRing 𝒜]
    {I p : Ideal R}
    (hI : I.IsHomogeneous 𝒜)
    (hp : p ∈ I.minimalPrimes) :
    p.IsHomogeneous 𝒜 := by sorry
