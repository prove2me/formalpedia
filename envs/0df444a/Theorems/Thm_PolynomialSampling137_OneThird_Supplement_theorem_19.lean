-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_theorem_19
-- name    : PolynomialSampling137.OneThird.Supplement.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:52:24.976248+00:00
-- url     : https://prove2.me/theorems/f1380701-c9b6-4c25-85f6-105c06c434a9
-- title:
--   Theorem 19 — Dyadic AND-product separation with exact exponent 2^(−3d−10)
-- statement:
--   For every $d\ge1$, put $p=2^{-(d+1)}$. For every $n\ge1$, $s\ge0$ and coordinatewise degree-at-most-$d$ map $Q:\mathbb F_2^s\to\mathbb F_2^n$,
--   $$\operatorname{Ov}(P_Q,\operatorname{Ber}(p)^{\otimes n})\le\exp(-2^{-3d-10}n).$$
--   There is no source support, independence, locality or seed-length restriction. This companion theorem separates degree-$d$ sources from products sampled exactly by $(d+1)$-input ANDs.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 19, printed p. 23; PDF p. 25

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem theorem_19 (d : ℕ) (hd : 1 ≤ d) (n s : ℕ) (hn : 1 ≤ n)
    (Q : Word s → Word n) (hQ : MapDegreeLE d Q) :
    overlap (samplerMass Q) (bernoulliProductMass ((2 : ℝ) ^ (-((d : ℤ) + 1))) n) ≤
      Real.exp (-((2 : ℝ) ^ (-3 * (d : ℤ) - 10)) * n) := by sorry

end PolynomialSampling137.OneThird.Supplement
