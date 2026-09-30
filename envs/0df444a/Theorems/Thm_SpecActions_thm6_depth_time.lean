-- Prove2me | Theorems.Thm_SpecActions_thm6_depth_time
-- name    : SpecActions.thm6_depth_time
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T19:08:57.808287+00:00
-- url     : https://prove2.me/theorems/cfd87612-97db-4086-9911-94067f481e65
-- title:
--   Theorem 6 — depth-focused time savings
-- statement:
--   Under the depth-focused policy, with deterministic real-call latency $a$ and speculative latency $b<a$, and per-step guess correctness probability $p$,
--
--   $$\frac{\mathbb{E}[T_{\mathrm{seq}}-T_{\mathrm{spec}}]}{\mathbb{E}[T_{\mathrm{seq}}]}=\frac{T-1}{T}\,p\left(1-\frac{b}{a}\right)$$
--
--   for every $T\ge 1$. The latency coefficient is $p$, against $\frac{p}{1+p}$ for breadth speculation, so the theoretical speedup ceiling rises from $\frac12$ to $1$. The number of active branches stays bounded because the system can run at most $a/b$ speculative steps ahead and inconsistent subtrees are pruned immediately.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Theorem 6, Appendix C.4 (pp. 23–24), time-savings expression; quoted in §5.3 (p. 10)

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem thm6_depth_time (T : ℕ) (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : 1 ≤ T) :
    (depthSeqTime T a - depthSpecTime T a b p) / depthSeqTime T a
      = ((T : ℝ) - 1) / (T : ℝ) * p * (1 - b / a) := by sorry
end SpecActions
