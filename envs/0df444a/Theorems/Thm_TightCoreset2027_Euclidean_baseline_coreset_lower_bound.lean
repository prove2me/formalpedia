-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_baseline_coreset_lower_bound
-- name    : TightCoreset2027.Euclidean.baseline_coreset_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:42:39.410282+00:00
-- url     : https://prove2.me/theorems/0643494a-0695-440d-8213-276654919498
-- title:
--   The Euclidean linear-in-k inverse-square-error boundary bound
-- statement:
--   For each fixed real $z\ge1$, there is a constant $c_z>0$ such that, for every integer $k\ge1$ and every $0<\varepsilon<1$, a finite dataset in some positive Euclidean dimension forces every strong subset coreset with arbitrary nonnegative weights to satisfy
--
--   $$|S|\ge c_z k\varepsilon^{-2}.$$
--
--   For errors below one half this is the subset, zero-offset specialization of CALSS22 Theorem11. The remaining error range is covered by the $k$-point argument used in §2.3 and §2.5 of the mission source. This boundary result supplies parameter regimes in which rounding prevents use of the multi-level construction.
-- source:
--   Cohen-Addad–Larsen–Saulpic–Schwiegelshohn, Towards Optimal Lower Bounds for k-median and k-means Coresets, arXiv:2202.12793, Theorem11 (Euclidean lower bound); https://cs.au.dk/~larsen/papers/CoreSetKMeans.pdf . Used by Hu–Huang–Li–Xu, STOC2027 submission879, §2.3 printed p.16 and §2.5 printed p.20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_generalPowers
open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean
 theorem baseline_coreset_lower_bound (z : ℝ) (hz : 1 ≤ z) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ d : ℕ, 1 ≤ d ∧ ∃ X : Finset (Point d),
        ∀ (S : Finset (Point d)) (w : Point d → NNReal),
          IsStrongCoreset z ε k X S w →
            c * (k : ℝ) * Real.rpow ε (-2) ≤ (S.card : ℝ) := by sorry
end TightCoreset2027.Euclidean
