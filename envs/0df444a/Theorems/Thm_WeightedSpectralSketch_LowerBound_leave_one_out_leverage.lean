-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_leave_one_out_leverage
-- name    : WeightedSpectralSketch.LowerBound.leave_one_out_leverage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:43.023461+00:00
-- url     : https://prove2.me/theorems/91578aa2-3a65-4bf4-a697-a1c7d540e1c1
-- title:
--   Lemma 3.1 — leave-one-out leverage averaging
-- statement:
--   Let $U=[u_1\cdots u_m]$ be a real matrix with columns $u_i$ and let $I$ be uniformly random in $[m]$. Then
--
--   $$
--   \Pr\big\{\mathrm{lev}_{u_I}(U_{-I})>1\big\}\le\frac{2\,\mathrm{rank}(U)}{m},
--   $$
--
--   where $U_{-i}$ removes the $i$-th column. The event includes infinite leave-one-out leverage ($u_I$ not in the span of the other columns), and no full-rank assumption is made.
--
--   When the number of columns is much larger than the rank, a uniformly chosen column is cheaply represented by the others; this is the averaging argument behind Lemmas 5.3, 5.4 and 6.2.
--
--   **Formalization Note.** The probability is the fraction of indices $i\in\mathrm{Fin}\,m$ with $\mathrm{lev}_{u_i}(U_{-i})>1$.
--
--   Differences from the source:
--
--   - generalization: I uniformly random among [m] (so m ≥ 1) → any m, including m = 0; reason: for m = 0 both sides are 0; for m ≥ 1 it is the source's statement
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 8, Lemma 3.1, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Leverage

open Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 3.1, p. 8: for `U = [u₁ ⋯ u_m]` and `I` uniform on `[m]`,
`Pr{lev_{u_I}(U_{-I}) > 1} ≤ 2 rank(U) / m`. -/
theorem leave_one_out_leverage {d : Type*} [Fintype d] {m : ℕ} (U : Fin m → d → ℝ) :
    (((Finset.univ.filter fun i : Fin m =>
        1 < lev (fun j : {j : Fin m // j ≠ i} => U j.1) (U i)).card : ℕ) : ℝ) / m ≤
      2 * ((colMat U).rank : ℝ) / m := by sorry

end WeightedSpectralSketch.LowerBound
