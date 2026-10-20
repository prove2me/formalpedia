-- Prove2me | Theorems.Thm_PermanentRollout_exists_sourceSeparatedBlockMinorSum_slicedGradient
-- name    : PermanentRollout.exists_sourceSeparatedBlockMinorSum_slicedGradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/6fd71ebe-e012-4e80-9af4-d05be99b0160
-- title:
--   PermanentRollout.exists_sourceSeparatedBlockMinorSum_slicedGradient
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.exists_sourceSeparatedBlockMinorSum_slicedGradient
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (hscale : 4 * powerSumParameter d ≤
      blockWidth d * blockColumns n d)
    (weight : Fin (blockCount n d) → ℂ)
    (hw : ∀ h, weight h ≠ 0) :
    ∃ (W : (Fin (sliceRank n d) → ℂ) →ₗ[ℂ]
          (Fin (blockVariables n d) → ℂ))
      (A : (Fin (blockVariables n d) → ℂ) →ₗ[ℂ]
          (Fin (sliceRank n d) → ℂ)),
      Function.Injective W ∧
      (∀ i : Fin (sliceRank n d),
        (slicedGradientPolynomial
          (sourceSeparatedBlockMinorSum n d weight) W A i).IsHomogeneous
            (d - 1)) ∧
      (∀ u : Fin (sliceRank n d) → ℂ,
        (∀ i : Fin (sliceRank n d),
          MvPolynomial.eval u
            (slicedGradientPolynomial
              (sourceSeparatedBlockMinorSum n d weight) W A i) = 0) ↔
                u = 0) := by sorry
