-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_lev_le_one_iff
-- name    : WeightedSpectralSketch.LowerBound.lev_le_one_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:49.136613+00:00
-- url     : https://prove2.me/theorems/00c56114-2773-4fab-946c-6bdea50f6c1d
-- title:
--   Lemma 3.2 — $\mathrm{lev}_v(U)\le1$ iff $vv^\top\preceq UU^\top$
-- statement:
--   For a real matrix $U$ with finitely many columns and a vector $v$ of matching dimension,
--
--   $$
--   \mathrm{lev}_v(U)\le1\iff vv^\top\preceq UU^\top ,
--   $$
--
--   where $M\preceq N$ means that $N-M$ is positive semidefinite. In particular both sides fail when $v\notin\mathrm{range}(U)$ (the leverage is then $+\infty$), and $U$ may be singular.
--
--   This characterization turns leverage bounds into Loewner-order bounds and back; it is used to build the incidence decomposition of Lemma 6.3.
--
--   Differences from the source: none.
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 8, Lemma 3.2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Leverage

open Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 3.2, p. 8: `lev_v(U) ≤ 1` if and only if `v vᵀ ⪯ U Uᵀ`. -/
theorem lev_le_one_iff {ι d : Type*} [Fintype ι] [Fintype d] (U : ι → d → ℝ) (v : d → ℝ) :
    lev U v ≤ 1 ↔ (colMat U * (colMat U)ᵀ - vecMulVec v v).PosSemidef := by sorry

end WeightedSpectralSketch.LowerBound
