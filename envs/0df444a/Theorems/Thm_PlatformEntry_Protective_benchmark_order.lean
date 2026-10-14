-- Prove2me | Theorems.Thm_PlatformEntry_Protective_benchmark_order
-- name    : PlatformEntry.Protective.benchmark_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:21.647521+00:00
-- url     : https://prove2.me/theorems/fefd602e-9fa4-4d15-9df0-ef7a2addc317
-- title:
--   Proof of Proposition 3, PDF p. 36 — e^B_N(a) ≥ e^B_E(a) for every a > 0 when H ≤ 1/4
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$, $c_S>1/2$, and suppose $(\delta,f,\beta)$ is in the protective regime $H\le 1/4$. Then for every base value $a>0$
--   $$e^B_E(a)\le e^B_N(a),$$
--   where $e^B_N$ and $e^B_E$ are the benchmark efforts (9) and (10).
--
--   In the protective regime the seller's first-best effort when the platform is sure to enter is no larger than when it is sure to stay out. In the proof of Proposition 3 this gives $dM/da\ge0$ at $a=\underline a_1$.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Proposition 3, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- Proof of Proposition 3, PDF p. 36: e^B_N(a) − e^B_E(a) ≥ 0 for any a > 0 when PlatformEntry.Regimes.H ≤ 1/4. -/
theorem benchmark_order (δ f β cS : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS)
    (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) :
    ∀ a : ℝ, 0 < a → eBE δ f β cS a ≤ eBN f cS a := by sorry

end PlatformEntry.Protective
