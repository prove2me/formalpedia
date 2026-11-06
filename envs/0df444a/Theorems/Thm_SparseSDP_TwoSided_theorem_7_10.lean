-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_theorem_7_10
-- name    : SparseSDP.TwoSided.theorem_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:28.727585+00:00
-- url     : https://prove2.me/theorems/554725a2-1702-42b2-ae18-77109b1e9b29
-- title:
--   Theorem 7.10, p. 59 — the constraint-side guarantee
-- statement:
--   In a run of Algorithm 7, with $\Lambda=\log(16mn/\delta)$, $B=c_BR\omega\sqrt{T/\Lambda}$ and $\eta_y=c_y\min\{1/B,\sqrt{\log(2m)/(R^2\omega^2T)}\}$, $c_y\le1$ (so $\eta_yB\le1$), with probability at least $1-\delta/3$,
--   $$
--   E_y(T)\le O\big(Rr\omega\sqrt{T\Lambda}\big).
--   $$
--
--   It balances the clipping level against the learning rate.
--
--   Differences from the source:
--   - reading: $B=\Theta(\cdot)$, $\eta_y=\Theta(\cdot)$, $O(\cdot)$ → for all constants $c_B>0$, $c_y\in(0,1]$ in `Consts` there is $C$; reason: the meaning of the $\Theta$ with the sufficiently small constant of the page
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Theorem 7.10, p. 59, Eq. (329)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Trajectory

open Matrix MeasureTheory

namespace SparseSDP.TwoSided

/-- **Theorem 7.10** (Constraint-Side Guarantee), p. 59.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Theorem 7.10, p. 59.

`B = c_B Rω√(T/Λ)` and `η_y = c_y min{1/B, √(log(2m)/(R²ω²T))}` with `c_y ≤ 1`, so `η_y B ≤ 1`. For
every choice of the `Θ` constants there is `C` with the bound (329) on `E_y(T)` of Eq. (330), except
with probability `δ/3`. -/
theorem theorem_7_10 (P : Consts) : ∃ C : ℝ, 0 < C ∧
    ∀ {d k : ℕ} [NeZero d] [NeZero k] (M : Fin k → Mat d) (acc : RowAccess d k) (s : ℕ)
      (c ω R r δ : ℝ) (T : ℕ), Alg7Hyp M acc s c ω R r δ → 1 ≤ T →
      tapeLaw {tape | ¬ Ey M R r (traj P acc s ω R r T δ tape) ≤
          C * (R * r * ω * √(T * lamP k d δ))} ≤
        ENNReal.ofReal (δ / 3) := by sorry

end SparseSDP.TwoSided
