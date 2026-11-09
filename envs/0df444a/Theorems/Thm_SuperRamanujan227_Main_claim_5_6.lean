-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_claim_5_6
-- name    : SuperRamanujan227.Main.claim_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:34.752347+00:00
-- url     : https://prove2.me/theorems/88035f81-aadf-4cdd-a08e-ef13d8a2c40e
-- title:
--   Claim 5.6 — Jacobi root bound for the largest root of $Q_{n,d}$
-- statement:
--   Let $d\ge3$ and $n\ge2$ be integers with $nd$ even, and let $x_{n,d}$ be the largest root of $Q_{n,d}$. Then
--   $$\frac{2\sqrt{d-1}}{d}-x_{n,d}>\frac{3}{4^{1/3}}\,n^{-2/3}\,\frac{(d-2+2/n)^{4/3}}{(d-1+1/n)^{1/6}\,\big(d^2+4(d-1)/n+4/n^2\big)^{5/6}}.$$
--   The inequality is strict. The case of odd $n$ with even $d$ is included.
--
--   It quantifies how far the largest root of the configuration-model polynomial lies below the normalized Ramanujan threshold $2\sqrt{d-1}/d$; Theorem 1.1 follows by simplifying the right-hand side.
--
--   Differences from the source:
--   - encoding: x_{n,d} the largest root of Q_{n,d} → the largest real root of Q_{n,d} (shared α_1); reason: Q_{n,d} is real-rooted of degree n ≥ 2, so α_1 is its largest root
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Claim 5.6, p. 20

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_Jacobi
open Polynomial

namespace SuperRamanujan227.Main

/-- Claim 5.6 (Jacobi root bound, p. 20): for `d ≥ 3`, `n ≥ 2`, `nd` even, the largest root
`x_{n,d}` of `Q_{n,d}` satisfies
`2√(d-1)/d - x_{n,d} > 3/4^{1/3} · n^{-2/3} · (d - 2 + 2/n)^{4/3} /
  ((d - 1 + 1/n)^{1/6} (d² + 4(d-1)/n + 4/n²)^{5/6})`. -/
theorem claim_5_6 (n d : ℕ) (hd : 3 ≤ d) (hn : 2 ≤ n) (hnd : Even (n * d)) :
    2 * Real.sqrt ((d : ℝ) - 1) / (d : ℝ) - kthLargestRoot (Q n d) 1 >
      3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) *
        (((d : ℝ) - 2 + 2 / (n : ℝ)) ^ ((4 : ℝ) / 3) /
          (((d : ℝ) - 1 + 1 / (n : ℝ)) ^ ((1 : ℝ) / 6) *
            ((d : ℝ) ^ 2 + 4 * ((d : ℝ) - 1) / (n : ℝ) + 4 / (n : ℝ) ^ 2) ^ ((5 : ℝ) / 6))) := by sorry

end SuperRamanujan227.Main
