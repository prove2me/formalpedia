-- Prove2me | Theorems.Thm_Shoppertainment_OptimalBandwidth_lemma_4
-- name    : Shoppertainment.OptimalBandwidth.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:16.868985+00:00
-- url     : https://prove2.me/theorems/a74ab894-8bd4-4222-8a6b-e6ddd2b28d03
-- title:
--   Lemma 4, p. 32 — π first decreases then increases in te, maximal at te = 0 and te = 1; π increases with q̲
-- statement:
--   Let $0 < \alpha < 1$ and $v > 0$, and let $\pi(t_e)$ be the streamer's individual profitability under the manufacturers' equilibrium prices, for a quality threshold $\underline q$.
--
--   1. For every $\underline q \in [0, 1)$ there is a turning point $t^\pi_e \in (\hat t_e, 1)$, with $\hat t_e = 1/(2-\underline q)$, such that $\pi$ is strictly decreasing on $[0, t^\pi_e]$ and strictly increasing on $[t^\pi_e, 1]$; and both endpoints maximize $\pi$ on $[0,1]$:
--   $$\pi(t_e) \le \pi(0) \quad\text{and}\quad \pi(t_e) \le \pi(1) \qquad \text{for all } t_e \in [0,1].$$
--   2. For every $t_e \in [0,1]$, $\pi$ is strictly increasing in the quality threshold $\underline q$ on $[0,1)$.
--
--   A streamer that cared only about profit per attending consumer would choose an extreme bandwidth; a higher quality threshold always raises that profit.
--
--   **Formalization Note** The paper's "$\partial \pi/\partial \underline q > 0$" is stated as strict monotonicity in $\underline q$, without derivatives. The turning point is stated by its defining property, inside the open interval $(\hat t_e, 1)$.
-- source:
--   Gu, Zhao & Wu, A Model of Shoppertainment Live Streaming, accepted manuscript (Management Science, forthcoming, Oct. 2024), p. 32, Lemma 4; proof in Online Supplementary A.6, pp. S4–S5 (PDF 53–54)

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

namespace Shoppertainment.OptimalBandwidth

theorem lemma_4 (α v : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v) :
    (∀ ql : ℝ, 0 ≤ ql → ql < 1 →
      (∃ tπ ∈ Set.Ioo (teHat ql) 1,
          StrictAntiOn (profitability α v ql) (Set.Icc 0 tπ) ∧
          StrictMonoOn (profitability α v ql) (Set.Icc tπ 1)) ∧
        IsMaxOn (profitability α v ql) (Set.Icc 0 1) 0 ∧
        IsMaxOn (profitability α v ql) (Set.Icc 0 1) 1) ∧
    (∀ te ∈ Set.Icc (0:ℝ) 1,
      StrictMonoOn (fun ql => profitability α v ql te) (Set.Ico 0 1)) := by sorry

end Shoppertainment.OptimalBandwidth
