-- Prove2me | Theorems.Thm_RiskUncSets_InnerApprox_mix_mem_restrictedSimplex_iff
-- name    : RiskUncSets.InnerApprox.mix_mem_restrictedSimplex_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:02.879657+00:00
-- url     : https://prove2.me/theorems/8e97d38a-4014-4c9c-83fc-4c08c15dadd1
-- title:
--   Proof of Theorem 4.5, pp. 1493–1494 — for λ ≥ 0, λq̂ + (1 − λ)e_N ∈ Δ̂ᴺ iff λ ≤ 1/(1 − N q̂_min)
-- statement:
--   Let $N \ge 1$, let $\hat q \in \hat\Delta^N$ (a probability vector with $\hat q_1 \ge \dots \ge \hat q_N$), let $\hat q_{\min} = \min_i \hat q_i$, and assume $N\hat q_{\min} < 1$ (that is, $\hat q \ne e_N$). Then for every $\lambda \ge 0$,
--   $$\lambda\hat q + (1-\lambda)e_N \in \hat\Delta^N \iff \lambda \le \frac{1}{1 - N\hat q_{\min}}.$$
--
--   This is the step "in order for $q$ to correspond to a distortion risk measure, it must have nonnegative components" of the proof of Theorem 4.5: the distortion risk measures of the paper (under Assumption 4.1) are exactly the $\mu_q$ with $q \in \hat\Delta^N$ (Theorem 4.2), and the bound (16) is where the mixture leaves $\hat\Delta^N$.
--
--   **Formalization Note** $\hat q_{\min}$, not defined on the page, is read as $\min_i \hat q_i$ (`⨅ i, qh i` over the nonempty finite index set; for $\hat q \in \hat\Delta^N$ it is $\hat q_N$). The hypothesis $N\hat q_{\min} < 1$ is added because (16) divides by $1 - N\hat q_{\min}$, which vanishes exactly when $\hat q = e_N$. The hypothesis $\lambda \ge 0$ is added: for $\lambda < 0$ the mixture is nondecreasing and lies outside $\hat\Delta^N$ unless $\hat q = e_N$; Theorem 4.5 only uses $\lambda^* \ge 0$.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), pp. 1493–1494, proof of Theorem 4.5, (16)

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Proof of Theorem 4.5, bound (16): for `q̂ ∈ Δ̂ᴺ` with `N q̂_min < 1` and `λ ≥ 0`,
`λq̂ + (1−λ)e_N ∈ Δ̂ᴺ` iff `λ ≤ 1/(1 − N q̂_min)`. -/
theorem mix_mem_restrictedSimplex_iff {N : ℕ} (hN : 0 < N) (qh : Fin N → ℝ)
    (hqh : qh ∈ restrictedSimplex N) (hmin : (N : ℝ) * (⨅ i, qh i) < 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    mix qh lam ∈ restrictedSimplex N ↔ lam ≤ 1 / (1 - (N : ℝ) * ⨅ i, qh i) := by sorry

end RiskUncSets.InnerApprox
