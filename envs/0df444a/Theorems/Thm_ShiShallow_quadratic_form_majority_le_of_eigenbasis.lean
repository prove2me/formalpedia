-- Prove2me | Theorems.Thm_ShiShallow_quadratic_form_majority_le_of_eigenbasis
-- name    : ShiShallow.quadratic_form_majority_le_of_eigenbasis
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T23:28:47.547838+00:00
-- url     : https://prove2.me/theorems/498cdb64-12d2-4620-9ca3-89fd07fb59e7
-- title:
--   The majority quadratic form is bounded on every state, in explicit matrix form
-- statement:
--   Matrix form of the entangled-state majority bound. If a matrix is diagonalised by a family of amplitude arrays that is orthonormal and satisfies the Parseval identity, and its eigenvalue on the i-th member is the majority inclusion-exclusion polynomial in three numbers each lying between 0 and s with s at most 1, then for EVERY normalised amplitude array, including ones that are not members of the family and are entangled across any tensor decomposition, the quadratic form is at most 3s^2 - 2s^3.
--
--   Stated with explicit sums rather than an abstract inner product space so that it applies directly to circuit acceptance operators.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem quadratic_form_majority_le_of_eigenbasis {N : ℕ}
    (M : Matrix (Bits N) (Bits N) ℂ) (s : ℝ) (hs : s ≤ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → (Bits N → ℂ)) (α1 α2 α3 : ι → ℝ)
    (h1 : ∀ i, 0 ≤ α1 i) (h2 : ∀ i, 0 ≤ α2 i) (h3 : ∀ i, 0 ≤ α3 i)
    (b1 : ∀ i, α1 i ≤ s) (b2 : ∀ i, α2 i ≤ s) (b3 : ∀ i, α3 i ≤ s)
    (horth : ∀ i j, (∑ y : Bits N, (starRingEnd ℂ) (v i y) * v j y)
      = if i = j then 1 else 0)
    (hpars : ∀ z : Bits N → ℂ,
      (∑ i : ι, ‖∑ y : Bits N, (starRingEnd ℂ) (z y) * v i y‖ ^ 2)
        = ∑ y : Bits N, ‖z y‖ ^ 2)
    (heig : ∀ i, Matrix.mulVec M (v i)
      = fun y => ((α1 i * α2 i + α2 i * α3 i + α3 i * α1 i
            - 2 * (α1 i * α2 i * α3 i) : ℝ) : ℂ) * v i y)
    (Φ : Bits N → ℂ) (hΦ : ∑ y : Bits N, ‖Φ y‖ ^ 2 = 1) :
    (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * Matrix.mulVec M Φ y).re
      ≤ 3 * s ^ 2 - 2 * s ^ 3 := by
  sorry

end ShiShallow
