-- Prove2me | Theorems.Thm_SpecActions_thm6_depth_cost
-- name    : SpecActions.thm6_depth_cost
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T19:14:07.852984+00:00
-- url     : https://prove2.me/theorems/f1d8fea0-c9ce-4eac-a8ed-9f2c9717730f
-- title:
--   Theorem 6 — depth-focused relative cost
-- statement:
--   Under the depth-focused policy with deterministic latencies $b<a$ and correctness probability $p$, the relative cost increase is exactly
--
--   $$\frac{\mathbb{E}[M_{\mathrm{spec}}-M_{\mathrm{seq}}]}{\mathbb{E}[M_{\mathrm{seq}}]}=\frac{T-1}{T}\cdot\frac{(1-p)\left(a\lfloor a/b\rfloor-b\,\frac{(1+\lfloor a/b\rfloor)\lfloor a/b\rfloor}{2}\right)+p\,b\lfloor a/b\rfloor}{a}$$
--
--   for every $T\ge 1$. A step whose guess is correct spends $a+\lfloor a/b\rfloor b$; a step whose guess is wrong also pays for the branches spawned before the real response arrived, the series $a+(a-b)+\cdots+(a-\lfloor a/b\rfloor b)$.
--
--   This is the **exact** identity. The paper immediately replaces it with the approximation $\frac{T-1}{T}\left((1-p)\left(\frac{a}{2b}-\frac12\right)+p\right)$, which agrees with the exact expression only when $a/b$ is an integer; the milestone asserts the exact floor version, which is what the proof establishes.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Theorem 6, Appendix C.4 (pp. 23–24), exact cost expression before the $\approx$ simplification

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem thm6_depth_cost (T : ℕ) (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : 1 ≤ T) :
    (depthSpecCost T a b p - depthSeqCost T a) / depthSeqCost T a
      = ((T : ℝ) - 1) / (T : ℝ) *
          ((1 - p) * (a * ⌊a / b⌋ - b * ((1 + ⌊a / b⌋) * ⌊a / b⌋ / 2))
            + p * (b * ⌊a / b⌋)) / a := by sorry
end SpecActions
