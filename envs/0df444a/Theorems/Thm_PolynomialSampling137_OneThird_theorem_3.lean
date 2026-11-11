-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_theorem_3
-- name    : PolynomialSampling137.OneThird.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T10:27:23.715239+00:00
-- url     : https://prove2.me/theorems/4d32a3d2-f8fb-4671-b658-54410db47007
-- title:
--   Theorem 3 — exponential separation from a product distribution
-- statement:
--   Fix a real $p\in(0,1)$, integer $t\ge1$, and $\delta>0$. Put $K=2^t$ and $m=\max\{p,1-p\}$. Let $Q:\mathbb F_2^s\to\mathbb F_2^n$ be any map for which every coordinate mean on every labeled affine $t$-cube differs from $p$ by at least $\delta$. If $\delta^2>p(1-p)/K$, then
--
--   $$\operatorname{Ov}(Q(U_s),\operatorname{Ber}(p)^{\otimes n})\le\exp\!\left(-\frac{2}{m^2K}\left(\delta^2-\frac{p(1-p)}K\right)^2n\right).$$
--
--   This statement allows arbitrary finite seed and output lengths and imposes no degree condition. The cube hypothesis includes every direction tuple, including degenerate ones. It is the general conditional amplification result used by the unconditional goal.
--
--   Differences from the source:
--   - encoding: actual sampler push-forward, independent Bernoulli target, and all labeled affine cubes → computed fiber masses, coordinate product masses, and CubeGap over Fin-indexed binary words; reason: finite sums encode the same distributions and all cube parameters without independence assumptions on sampler outputs
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 3 Eqs. (11)–(12), printed p. 10 / PDF p. 12; proof printed p. 11 / PDF p. 13

import Definitions.Def_PolynomialSampling137_OneThird_FiniteProbability
import Definitions.Def_PolynomialSampling137_OneThird_AffineCubes

namespace PolynomialSampling137.OneThird

/-- Zhong, Theorem 3, with its strict threshold and exact exponent. -/
theorem theorem_3 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : ℕ) (ht : 1 ≤ t) (δ : ℝ) (hδ : 0 < δ)
    (s n : ℕ) (Q : Word s → Word n) (hgap : CubeGap t p δ Q)
    (hthreshold : p * (1 - p) / (2 : ℝ) ^ t < δ ^ 2) :
    overlap (samplerMass Q) (bernoulliProductMass p n) ≤
      Real.exp (-(2 / ((max p (1 - p)) ^ 2 * (2 : ℝ) ^ t)) *
        (δ ^ 2 - p * (1 - p) / (2 : ℝ) ^ t) ^ 2 * (n : ℝ)) := by sorry

end PolynomialSampling137.OneThird
