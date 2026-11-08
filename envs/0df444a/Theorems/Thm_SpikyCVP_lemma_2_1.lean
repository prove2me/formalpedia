-- Prove2me | Theorems.Thm_SpikyCVP_lemma_2_1
-- name    : SpikyCVP.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:52:32.233496+00:00
-- url     : https://prove2.me/theorems/a9908352-fb43-47b1-b3a1-2058fab85752
-- title:
--   Lemma 2.1 — rounding a real basis
-- statement:
--   Let $B\in\mathbb R^{n\times k}$ be the basis of a full column rank lattice, with minimum singular value $\sigma_{\min}(B)$. Suppose that for $b\in\mathbb N$ the matrix $\hat B\in\mathbb Q^{n\times k}$ satisfies $\max_{i,j}|B_{ij}-\hat B_{ij}|\le2^{-b}$. Then for every $z\in\mathbb Z^k$,
--
--   $$\|\hat Bz-Bz\|_2\le\frac{\sqrt{nk}\,2^{-b}}{\sigma_{\min}(B)}\,\|Bz\|_2 .$$
--
--   The algorithm calls a Euclidean CVP solver on lattices with real bases $\mathrm{diag}(1/s)B$; this lemma bounds the distortion caused by rounding such a basis to rational entries.
--
--   Differences from the source:
--   - encoding: minimum singular value σmin(B) → the published DissolveCDF.sigmaMin of B viewed as a linear map between Euclidean spaces, the infimum of ∥Bν∥₂ over unit vectors ν; reason: for a matrix with linearly independent columns this is the smallest singular value
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 2.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_SpikyCVP_latt
import Definitions.Def_DissolveCDF_sigmaMin

open PNormReg

namespace SpikyCVP

/-- **Lemma 2.1 (rounding a basis).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 2.1, p.10 (PDF p.12).

Let `B ∈ ℝ^{n×k}` be the basis of a full column rank lattice, with minimum singular value `σmin(B)`.
If `b ∈ ℕ` and `B̂ ∈ Q^{n×k}` satisfy `max_{i,j} |B_ij − B̂_ij| ≤ 2^{−b}`, then for every `z ∈ Z^k`,
`∥B̂z − Bz∥2 ≤ (√(nk) 2^{−b} / σmin(B)) ∥Bz∥2`.

**Formalization Note.** Full column rank is linear independence of the columns. `σmin(B)` is the published
`DissolveCDF.sigmaMin`, `inf {∥Bν∥2 : ∥ν∥2 = 1}`, applied to `B` as a linear map `ℝ^k → ℝ^n` between
Euclidean spaces; for independent columns it is the smallest singular value. -/
theorem lemma_2_1 {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (hB : LinearIndependent ℝ B.transpose)
    (Bh : Matrix (Fin n) (Fin k) ℚ) (b : ℕ)
    (hb : ∀ i j, |B i j - (Bh i j : ℝ)| ≤ (2 : ℝ) ^ (-(b : ℤ))) (z : Fin k → ℤ) :
    l2Norm ((Bh.map fun q : ℚ => (q : ℝ)).mulVec (fun i => (z i : ℝ)) - B.mulVec (fun i => (z i : ℝ))) ≤
      Real.sqrt ((n : ℝ) * k) * (2 : ℝ) ^ (-(b : ℤ)) /
        DissolveCDF.sigmaMin (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)) *
        l2Norm (B.mulVec (fun i => (z i : ℝ))) := by sorry

end SpikyCVP
