-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_posIndex_le_trace_pinv
-- name    : WeightedSpectralSketch.LowerBound.posIndex_le_trace_pinv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:22.403693+00:00
-- url     : https://prove2.me/theorems/03812292-2dda-4c1b-bbd1-9727adaf4601
-- title:
--   Lemma 6.6 — positive inertia of $M-N$ is at most $2\,\mathrm{tr}((M+N)^\dagger M)$
-- statement:
--   For any real positive semidefinite matrices $M,N$ of the same dimension (possibly singular, possibly zero),
--
--   $$
--   n_+(M-N)\le2\,\mathrm{tr}\big((M+N)^\dagger M\big),
--   $$
--
--   where $n_+$ counts the strictly positive eigenvalues of the symmetric matrix $M-N$ with multiplicity and $(M+N)^\dagger$ is the Moore–Penrose pseudoinverse. (Here $N$ is a matrix, not the sketch dimension.)
--
--   Applied with $M=\sum_{w}a_{uw}a_{uw}^\top$ it bounds each $k_u$ by twice a sum of leverage scores, which drives Lemma 6.5.
--
--   **Formalization Note.** $n_+$ is the published `RHLinalg.posIndex` applied to the symmetric matrix $M-N$. The pseudoinverse is the spectral one of `hermPinv`.
--
--   Differences from the source: none.
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 24, Lemma 6.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_WeightedSpectralSketch_LowerBound_Leverage

open Matrix

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 6.6, p. 24: for real PSD matrices `M, N` of the same dimension,
`n₊(M - N) ≤ 2 tr((M + N)† M)`. -/
theorem posIndex_le_trace_pinv {n : Type*} [Fintype n] [DecidableEq n] (M N : Matrix n n ℝ)
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    (RHLinalg.posIndex (hM.isHermitian.sub hN.isHermitian) : ℝ) ≤
      2 * (hermPinv (hM.isHermitian.add hN.isHermitian) * M).trace := by sorry

end WeightedSpectralSketch.LowerBound
