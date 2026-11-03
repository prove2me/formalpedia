-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_14
-- name    : WeightedCongestionBR.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:42.04351+00:00
-- url     : https://prove2.me/theorems/36a14e4c-0f44-4ed4-abe7-9f574bbe0aa6
-- title:
--   Lemma 14 — the algebraic inequality behind Lemma 10
-- statement:
--   Fix a positive integer $d$. For any polynomial $f\in\mathfrak P_d$ and any $\varepsilon>0$,
--
--   $$
--   y\,f(z+x+y)\le(1+\varepsilon)\,y\,f(z+x'+y)+\Big(1+\frac1\varepsilon\Big)^d d^d\,x\,f(z+x+y')
--   $$
--
--   for any $x,x',y,y',z\ge0$. It is applied resource by resource in the proof of Lemma 10.
--
--   Differences from the source: none.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 14, p.27

import Mathlib
import Definitions.Def_WeightedCongestionBR_IsPd
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- **Lemma 14** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.27). Fix a positive integer `d`. For any polynomial `f ∈ 𝔓_d` and any
`ε > 0`,
`y f(z + x + y) ≤ (1 + ε) y f(z + x' + y) + (1 + 1/ε)^d d^d x f(z + x + y')`
for any `x, x', y, y', z ≥ 0`. -/
theorem lemma_14 (d : ℕ) (hd : 1 ≤ d) (f : Polynomial ℝ) (hf : IsPd d f) (ε : ℝ) (hε : 0 < ε)
    (x x' y y' z : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) (hy' : 0 ≤ y') (hz : 0 ≤ z) :
    y * f.eval (z + x + y) ≤
      (1 + ε) * y * f.eval (z + x' + y) + (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * f.eval (z + x + y') := by sorry

end WeightedCongestionBR
