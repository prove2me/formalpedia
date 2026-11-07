-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_3_20
-- name    : TimeSpaceMA.lemma_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:14.343941+00:00
-- url     : https://prove2.me/theorems/69d2d826-2f14-45af-ba0c-a88e1d0d75c8
-- title:
--   Lemma 3.20 — fast matrix multiplication
-- statement:
--   For every $\varepsilon>0$, two $h\times h$ integer matrices can be multiplied using $O(h^{\omega+\varepsilon})$ arithmetic operations. Consequently, for $1\le h\le k$, multiplying an $r\times k$ by a $k\times r'$ integer matrix can be done using
--   $$O\bigl((r/h+1)(r'/h+1)\,k\,h^{\omega-1+\varepsilon}\bigr)$$
--   operations, where $\omega$ is the matrix multiplication exponent.
--
--   Differences from the source:
--   - encoding: integer matrices and arithmetic operations → straight-line programs with coefficients in ℚ, into which integer matrices embed (published MatrixAlgorithm, cost counts +, −, ×); reason: the published vocabulary is over a field, and a correct program over ℚ is correct on integer matrices
--   - reading: ω, the matrix multiplication exponent, of unnamed field → ω = OAI omega ℂ, while the programs are over ℚ; reason: ω_ℂ is the field of the published bound 9/4 and, formally, ω_ℂ ≤ ω_ℚ, so this is the stronger clause; the two are equal by a classical transfer
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma 3.20, p.19

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

namespace TimeSpaceMA

open OAI.MatrixMultiplication.Arithmetic

/-- **Lemma 3.20** (Fast matrix multiplication; Williams, Xi, STOC 2027 submission, manuscript sha256
184c2f95…, p.19). For every `ε > 0`, `h × h` integer matrices can be multiplied using `O(h^{ω+ε})` arithmetic
operations; and for `1 ≤ h ≤ k`, an `r × k` by `k × r′` product takes
`O((r/h + 1)(r′/h + 1) k h^{ω−1+ε})` operations.

**Formalization Note** Programs have coefficients in `ℚ`, into which integer entries embed; the exponent is
`ω = omega ℂ` of the published vocabulary. Real division in the bound. `C` is one constant after `ε`. -/
theorem lemma_3_20 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∀ h : ℕ, 1 ≤ h → ∃ P : MatrixAlgorithm ℚ h h h,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (h : ℝ) ^ (omega ℂ + ε)) ∧
      (∀ h k r r' : ℕ, 1 ≤ h → h ≤ k → ∃ P : MatrixAlgorithm ℚ r k r',
        P.Correct ∧
          (P.cost : ℝ) ≤ C * ((r : ℝ) / h + 1) * ((r' : ℝ) / h + 1) * (k : ℝ) *
            (h : ℝ) ^ (omega ℂ - 1 + ε)) := by sorry

end TimeSpaceMA
