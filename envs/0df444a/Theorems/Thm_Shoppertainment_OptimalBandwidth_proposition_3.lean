-- Prove2me | Theorems.Thm_Shoppertainment_OptimalBandwidth_proposition_3
-- name    : Shoppertainment.OptimalBandwidth.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:06.662323+00:00
-- url     : https://prove2.me/theorems/a435276d-34cc-40d1-900b-353c1b8d5725
-- title:
--   Proposition 3, p. 33 — te = 0 is never optimal; t*_e ≥ t^T_e for ve ≤ v(1+q̲)/4; t*_e = 1 for ve > v(1+q̲)/4
-- statement:
--   Let $0 < \alpha < 1$ be the commission rate, $v > 0$ the good-fit value, $K > 0$ the attending-cost range, $0 \le \underline q < 1$ the quality threshold and $v_e \ge 0$ the streamer's entertaining capability. Let $T(t_e)$ be the attending traffic (13), $\pi(t_e)$ the individual profitability, and $\Pi(t_e) = T(t_e)\,\pi(t_e)$ the streamer's total payoff, all under the manufacturers' equilibrium prices. Then:
--
--   1. $t_e = 0$ is not a maximizer of $\Pi$ on $[0,1]$.
--   2. $\Pi$ attains its maximum on $[0,1]$.
--   3. If $v_e \le v(1+\underline q)/4$, then every maximizer $t^*_e$ of $\Pi$ on $[0,1]$ lies at or beyond every maximizer $t^T_e$ of the traffic $T$ on $[0,1]$: $t^*_e \in [t^T_e, 1]$.
--   4. If $v_e > v(1+\underline q)/4$, then $t_e = 1$ is the unique maximizer:
--   $$\Pi(t_e) < \Pi(1) \qquad \text{for every } t_e \in [0,1).$$
--
--   This is the paper's headline result: a commission-maximizing streamer never spends all bandwidth on product information, allocates at least as much to entertainment as would maximize traffic, and goes to full entertainment when its entertaining capability is high enough.
--
--   **Formalization Note** "Optimal" means a maximizer of $\Pi$ on $[0,1]$; existence is asserted separately so that part 3 is not vacuous. $t^T_e$ is quantified as an arbitrary maximizer of $T$ on $[0,1]$ rather than through the first-order condition of the Online Supplementary. $v_e \ge 0$ is as printed in Proposition 3 (Table 1 has $v_e > 0$); $\underline q < 1$ is pinned so the uniform quality law exists; $\alpha < 1$ is the standing range of p. 13. The paper's proof of part 4 (Online Supplementary A.7) shows only that $d\Pi/dt_e > 0$ at $t_e = 1$; the statement here is the full claim of uniqueness of the maximizer.
-- source:
--   Gu, Zhao & Wu, A Model of Shoppertainment Live Streaming, accepted manuscript (Management Science, forthcoming, Oct. 2024), p. 33, Proposition 3; proof in Online Supplementary A.7, pp. S5–S6 (PDF 54–55)

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

namespace Shoppertainment.OptimalBandwidth

theorem proposition_3 (α v ve K ql : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v) (hK : 0 < K)
    (hql : 0 ≤ ql) (hql1 : ql < 1) (hve : 0 ≤ ve) :
    ¬ IsMaxOn (payoff α v ve K ql) (Set.Icc 0 1) 0 ∧
    (∃ t ∈ Set.Icc (0:ℝ) 1, IsMaxOn (payoff α v ve K ql) (Set.Icc 0 1) t) ∧
    (ve ≤ v * (1 + ql) / 4 →
      ∀ tS ∈ Set.Icc (0:ℝ) 1, IsMaxOn (payoff α v ve K ql) (Set.Icc 0 1) tS →
      ∀ tT ∈ Set.Icc (0:ℝ) 1, IsMaxOn (traffic v ve K ql) (Set.Icc 0 1) tT → tT ≤ tS) ∧
    (v * (1 + ql) / 4 < ve →
      ∀ t ∈ Set.Ico (0:ℝ) 1, payoff α v ve K ql t < payoff α v ve K ql 1) := by sorry

end Shoppertainment.OptimalBandwidth
