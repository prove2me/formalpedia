-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_lemma_5_4
-- name    : SuperRamanujan227.Main.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:21.130193+00:00
-- url     : https://prove2.me/theorems/d3d1cf32-d224-4382-a314-c19cb411b202
-- title:
--   Lemma 5.4 — multiplicative convolution with $x^j(x-1)^{L-j}$ is a scaled derivative
-- statement:
--   Let $p$ be a real polynomial of degree $L$ and let $1\le j\le L$. Put $q(x)=x^j(x-1)^{L-j}$. Then
--   $$(p\boxtimes_L q)(x)=\frac{1}{(L)_j}\,x^j\,p^{(j)}(x),$$
--   where $(L)_j=L(L-1)\cdots(L-j+1)$ is the falling factorial and $p^{(j)}$ is the $j$-th derivative of $p$. No real-rootedness or monicity of $p$ is required.
--
--   In the proof of Theorem 1.1 this identifies the multiplicative convolution coming from the configuration model with a derivative of the matching polynomial.
--
--   Differences from the source:
--   - encoding: ⊠_L of Definition 2.4 → the MSS coefficient formula in degree L; reason: it agrees with Definition 2.4 on characteristic polynomials [MSS22] and extends it bilinearly to all polynomials of degree ≤ L, as the lemma (stated for arbitrary degree-L p) requires
--   - encoding: j ∈ [L] → 1 ≤ j ≤ L; reason: [L] = {1, …, L}
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Lemma 5.4 ([AGVP23, Lemma 3.5]), p. 18, Eq. (27)

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_FiniteFreeConvolution
open Polynomial

namespace SuperRamanujan227.Main

/-- Lemma 5.4 ([AGVP23, Lemma 3.5], p. 18): for a degree-`L` polynomial `p`, `j ∈ [L]` and
`q(x) = x^j (x - 1)^{L-j}`, `(p ⊠_L q)(x) = x^j p^{(j)}(x) / (L)_j`, with `(L)_j` the falling
factorial. -/
theorem lemma_5_4 (L j : ℕ) (p : ℝ[X]) (hp : p.natDegree = L) (hj : 1 ≤ j) (hjL : j ≤ L) :
    ffMul L p (X ^ j * (X - 1) ^ (L - j)) =
      C (1 / (L.descFactorial j : ℝ)) * X ^ j * derivative^[j] p := by sorry

end SuperRamanujan227.Main
