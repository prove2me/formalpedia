-- Prove2me | Theorems.Thm_Shoppertainment_OptimalBandwidth_proposition_2
-- name    : Shoppertainment.OptimalBandwidth.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:08.123798+00:00
-- url     : https://prove2.me/theorems/ce0a3a63-04dd-4afa-8869-7ebd18cb4b28
-- title:
--   Proposition 2, p. 27 — traffic T increases in te if ve > v(1+q̲)/2; otherwise it increases then decreases, peaking at t^T_e ∈ [t̂e, 1]
-- statement:
--   Let $v > 0$, $K > 0$, $0 \le \underline q < 1$ and entertaining capability $v_e > 0$, and let $T(t_e) = (v_e t_e + Eu_p(t_e))/K$ be the attending consumer traffic (13), with $Eu_p$ the consumer's expected shopping surplus under the manufacturers' equilibrium prices. Write $\hat t_e = 1/(2-\underline q)$.
--
--   1. If $v_e > v(1+\underline q)/2$, then $T$ is strictly increasing on $[0,1]$.
--   2. If $v_e \le v(1+\underline q)/2$, then there is $t^T_e \in [\hat t_e, 1]$ such that $T$ is strictly increasing on $[0, t^T_e]$ and strictly decreasing on $[t^T_e, 1]$:
--   $$T \nearrow \text{ on } [0, t^T_e], \qquad T \searrow \text{ on } [t^T_e, 1].$$
--
--   In particular, in the second case $t^T_e$ is the unique maximizer of the traffic on $[0,1]$. A strong entertainer gains traffic from every extra unit of entertainment, a weaker one loses traffic beyond the peak because deal prices disappear.
--
--   **Formalization Note** $v_e > 0$ is the standing range of Table 1 (p. 21) and is needed for strict increase on $[0, \hat t_e]$, where $T = v_e t_e/K$. The peak $t^T_e$, which the paper defines through a first-order condition in the Online Supplementary, is stated here by its defining property. At $v_e = v(1+\underline q)/2$ the decreasing part is the single point $t^T_e = 1$.
-- source:
--   Gu, Zhao & Wu, A Model of Shoppertainment Live Streaming, accepted manuscript (Management Science, forthcoming, Oct. 2024), p. 27, Proposition 2; proof in Online Supplementary A.4, pp. S3–S4 (PDF 52–53)

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

namespace Shoppertainment.OptimalBandwidth

theorem proposition_2 (v ve K ql : ℝ) (hv : 0 < v) (hK : 0 < K) (hql : 0 ≤ ql) (hql1 : ql < 1)
    (hve : 0 < ve) :
    (v * (1 + ql) / 2 < ve → StrictMonoOn (traffic v ve K ql) (Set.Icc 0 1)) ∧
    (ve ≤ v * (1 + ql) / 2 → ∃ tT ∈ Set.Icc (teHat ql) 1,
        StrictMonoOn (traffic v ve K ql) (Set.Icc 0 tT) ∧
        StrictAntiOn (traffic v ve K ql) (Set.Icc tT 1)) := by sorry

end Shoppertainment.OptimalBandwidth
