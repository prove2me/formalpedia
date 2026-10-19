-- Prove2me | Theorems.Thm_QApproxCount_Counting_lemma_2
-- name    : QApproxCount.Counting.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:22.070115+00:00
-- url     : https://prove2.me/theorems/4dbbda6c-a8d0-4ffc-823b-ef2fecc71fa2
-- title:
--   Lemma 2 (rotation lemma) — r from (45)–(47) is odd, 1 ≤ r ≤ 5/(γθ), and one update fails to keep θmin ≤ θ ≤ θmax with probability < δ
-- statement:
--   Let $0<\theta_{\min}\le\theta\le\theta_{\max}\le0.002$ with $\theta_{\max}=(1+\gamma)\theta_{\min}$ for some $0<\gamma\le0.7$, let $0<\delta<1$, and let $m\ge250\ln(\delta^{-1})$. Let $r$ be computed from $\theta_{\min},\theta_{\max}$ alone by eqs. (45)–(47). Then:
--
--   1. $r$ is an odd integer with $1\le r\le\dfrac{5}{\gamma\theta}$;
--   2. toss a coin with bias $\sin^2(r\theta)$ $m$ times and let $H$ be the number of heads. If $H>0.12m$, set $\theta_{\min}:=\theta_{\max}/(1+0.9\gamma)$; otherwise set $\theta_{\max}:=(1+0.9\gamma)\theta_{\min}$. The probability that the new bracket fails to contain $\theta$ is less than $\delta$;
--   3. the same holds when the test is $H\ge0.12m$ instead of $H>0.12m$.
--
--   That is,
--   $$\Pr\big[\theta\notin[\theta_{\min}',\theta_{\max}']\big]<\delta .$$
--
--   Each round of step 2 of the algorithm is one application of this lemma: it shrinks the ratio $\theta_{\max}/\theta_{\min}$ from $1+\gamma$ to $1+0.9\gamma$ at a cost of $O(\gamma^{-1}\theta^{-1}\log\delta^{-1})$ queries.
--
--   **Formalization Note** The lemma's "$r\in O(\theta^{-1}\gamma^{-1})$" is pinned to the explicit bound $r\le5/(\gamma\theta)$. The paper's proof gives $r\le\pi(1+\gamma)^2/(2\gamma\theta)+1<4.6/(\gamma\theta)$. The hypotheses $\gamma>0$ (eq. (46) divides by $\Delta\theta$) and $\delta<1$ (otherwise $250\ln\delta^{-1}\le0$) are implicit in the paper. The lemma's threshold is "more than 12%"; step 2(c) of the algorithm uses "at least 12%". Item 3 reconciles the two, so the lemma applies to the algorithm as printed. $r$ is the algorithm's `rotR`, a function of $\theta_{\min},\theta_{\max}$ only.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 8, Lemma 2 (proof pp. 9–10); threshold of step 2(c), p. 4

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Lemma 2 (rotation lemma), p. 8. Let `0 < θmin ≤ θ ≤ θmax ≤ 0.002` with
`θmax = (1 + γ) θmin`, `0 < γ ≤ 0.7`, let `0 < δ < 1`, and let `m ≥ 250 ln(δ⁻¹)` be the number of
tosses. The `r` computed from `θmin, θmax` alone by (45)–(47) (`rotR`) is an odd integer with
`1 ≤ r ≤ 5/(γθ)`, and, for the number of heads `h` in `m` tosses of a coin with bias `sin²(rθ)`,
the update "if the heads are more than 12% (resp. at least 12%, as in step 2(c)) set
`θmin := θmax/(1 + 0.9γ)`, otherwise set `θmax := (1 + 0.9γ) θmin`" leaves `θ` outside the new
bracket with probability less than `δ`, for both thresholds. -/
theorem lemma_2 (θmin θmax θ γ δ : ℝ) (hθmin : 0 < θmin) (hlo : θmin ≤ θ) (hhi : θ ≤ θmax)
    (hθmax : θmax ≤ 0.002) (hmax : θmax = (1 + γ) * θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 250 * Real.log δ⁻¹ ≤ (m : ℝ)) :
    Odd (rotR θmin θmax) ∧ 1 ≤ rotR θmin θmax ∧ (rotR θmin θmax : ℝ) ≤ 5 / (γ * θ) ∧
      (coin (Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | ¬ (if 0.12 * (m : ℝ) < (h : ℝ) then
                        θmax / (1 + 0.9 * γ) ≤ θ ∧ θ ≤ θmax
                      else θmin ≤ θ ∧ θ ≤ (1 + 0.9 * γ) * θmin)} < ENNReal.ofReal δ ∧
      (coin (Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | ¬ (if 0.12 * (m : ℝ) ≤ (h : ℝ) then
                        θmax / (1 + 0.9 * γ) ≤ θ ∧ θ ≤ θmax
                      else θmin ≤ θ ∧ θ ≤ (1 + 0.9 * γ) * θmin)} < ENNReal.ofReal δ := by sorry

end QApproxCount.Counting
