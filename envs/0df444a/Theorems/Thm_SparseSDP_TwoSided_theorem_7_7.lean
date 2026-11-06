-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_theorem_7_7
-- name    : SparseSDP.TwoSided.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:11.513506+00:00
-- url     : https://prove2.me/theorems/77c3c853-5db4-4de5-b4a1-40780f89ba55
-- title:
--   Theorem 7.7, p. 53 — the matrix-side guarantee
-- statement:
--   In a run of Algorithm 7 with $C_L$ sufficiently large, for every $\delta_X\in(0,1)$, with probability at least $1-\delta_X-\delta_L$, $\delta_L=\delta/3$,
--   $$
--   E_X(T)\le\frac{R\log(4n)}{\eta_X}+\frac{3R\eta_Xr^2\omega^2T}{2}+2Rr\omega\sqrt{2T\log\frac1{\delta_X}}+Rr\omega.
--   $$
--
--   It combines the regret of the mean response, rank-one sampling and the Lánczos error.
--
--   Differences from the source:
--   - reading: $C_L$ a sufficiently large universal constant → $\exists C_0$, for all `Consts` with $C_0\le C_L$; reason: the meaning of the phrase
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Theorem 7.7, p. 53, Eq. (277)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Trajectory

open Matrix MeasureTheory

namespace SparseSDP.TwoSided

/-- **Theorem 7.7** (Matrix-side guarantee), p. 53.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Theorem 7.7, p. 53.

With probability at least `1 − δ_X − δ_L`, `δ_L = δ/3`, Eq. (277) holds for `E_X(T)` of Eq. (278), for
`C_L` sufficiently large (it enters through Lemma 7.4). -/
theorem theorem_7_7 : ∃ C₀ : ℝ, ∀ (P : Consts), C₀ ≤ P.CL →
    ∀ {d k : ℕ} [NeZero d] [NeZero k] (M : Fin k → Mat d) (acc : RowAccess d k) (s : ℕ)
      (c ω R r δ δX : ℝ) (T : ℕ), Alg7Hyp M acc s c ω R r δ → 1 ≤ T → 0 < δX → δX < 1 →
      tapeLaw {tape | ¬ EX M R r (traj P acc s ω R r T δ tape) ≤
          R * Real.log (4 * d) / etaX d T r ω + 3 * R * etaX d T r ω * r ^ 2 * ω ^ 2 * T / 2 +
            2 * R * r * ω * √(2 * T * Real.log (1 / δX)) + R * r * ω} ≤
        ENNReal.ofReal (δX + δ / 3) := by sorry

end SparseSDP.TwoSided
