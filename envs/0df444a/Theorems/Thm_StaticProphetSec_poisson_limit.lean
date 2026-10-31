-- Prove2me | Theorems.Thm_StaticProphetSec_poisson_limit
-- name    : StaticProphetSec.poisson_limit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:35.144993+00:00
-- url     : https://prove2.me/theorems/563425e9-1527-4e34-ac2d-5c42b7b73e60
-- title:
--   (12), p.18 — $\mathbb E[f(\mathrm{Bin}(n,k/n))]\to\mathbb E[f(\mathrm{Pois}(k))]$ for bounded $f$
-- statement:
--   For $k\ge1$ and every bounded $f:\mathbb N_0\to\mathbb R$,
--
--   $$\lim_{n\to\infty}\mathbb E[f(\mathrm{Bin}(n,k/n))]=\mathbb E[f(\mathrm{Pois}(k))].$$
--
--   Taking $f=\mathrm{AR}_k$ gives (12), and $f=\mathrm{UT}_k$ gives the first equality of (51).
--
--   Differences from the source:
--
--   - generalization: $f=\mathrm{AR}_k$ in (12), $f=\mathrm{UT}_k$ in (51) → every bounded $f$; reason: both functions are bounded by $1$, so the statement specializes to both displays
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, (12), p.18; first equality of (51), p.38

import Mathlib
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE

open Filter Topology
open scoped NNReal

namespace StaticProphetSec

/-- The Poisson limit (Arnosti & Ma, arXiv:2108.12893v2, (12), p.18, and the first equality of
(51), p.38): for every bounded `f : ℕ → ℝ`, `E[f(Bin(n, k/n))] → E[f(Pois(k))]` as `n → ∞`.
Taking `f = AR_k` gives (12) and `f = UT_k` gives the equality in (51). -/
theorem poisson_limit (k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℝ) (hf : ∃ C : ℝ, ∀ d, |f d| ≤ C) :
    Tendsto (fun n : ℕ => pbE f (fun _ : Fin n => (k : ℝ) / (n : ℝ))) atTop
      (𝓝 (poisE f (k : ℝ≥0))) := by sorry

end StaticProphetSec
