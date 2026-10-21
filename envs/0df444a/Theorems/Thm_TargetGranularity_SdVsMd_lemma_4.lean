-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_lemma_4
-- name    : TargetGranularity.SdVsMd.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:56.294433+00:00
-- url     : https://prove2.me/theorems/b82962c5-d7bd-4294-aea6-cea0b9f9e03c
-- title:
--   Lemma 4, p. 40 (PDF 41) — the sd equilibrium profit is strictly decreasing in c_click on ((1−p)²/2,(1−p)/2) and is 0 at c_click = (1−p)/2
-- statement:
--   Let $0<p<1$ and $0<c_{ad}<p(1-p)$. Then:
--
--   1. for click costs $\frac{(1-p)^2}{2}<c_1<c_2<\frac{1-p}{2}$ and any non-trivial sd equilibria $\Sigma_1$ at $c_1$ and $\Sigma_2$ at $c_2$,
--   $$\Pi^{sd}(c_2;\Sigma_2)<\Pi^{sd}(c_1;\Sigma_1);$$
--   2. at $c_{click}=\frac{1-p}{2}$ the set $[\bar\alpha,1]$ with $\bar\alpha=\frac{p^2}{p-c_{ad}}$ is a non-trivial sd equilibrium, and its profit is $0$.
--
--   Together with Lemma 6 this gives a positive sd profit at click costs just below $c^{max}_{click}$, which is one side of Proposition 3.
--
--   **Formalization Note** The hypothesis $c_{ad}<p(1-p)$ is added: it is what makes $\bar\alpha=p^2/(p-c_{ad})<1$, so that the endpoint equilibrium is non-trivial; Lemma 6's $c_{ad}<\min\{p^2,p(1-p)\}$ implies it. "Decreasing" is read as strictly decreasing, and part 1 is on the open interval: at $c_{click}=(1-p)/2$ the ad value vanishes on $[\bar\alpha,1]$, so part 2 names the page's equilibrium instead of comparing all equilibria there.
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), p. 40 (PDF 41), Lemma 4, in the proof of Proposition 3

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Lemma 4, p. 40 (with the added `c_ad < p(1 − p)`): (a) on `((1−p)²/2, (1−p)/2)` the sd
equilibrium profit is strictly decreasing in `c_click`; (b) at `c_click = (1−p)/2` the set
`[p²/(p − c_ad), 1]` is a non-trivial sd equilibrium with profit `0`. -/
theorem lemma_4 (p cad : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcad : 0 < cad)
    (hcadp1 : cad < p * (1 - p)) :
    (∀ c₁ c₂ : ℝ, (1 - p) ^ 2 / 2 < c₁ → c₁ < c₂ → c₂ < (1 - p) / 2 →
      ∀ S₁ S₂ : Set ℝ, IsSdEq p cad c₁ S₁ → IsSdEq p cad c₂ S₂ →
        sdProfit p cad c₂ S₂ < sdProfit p cad c₁ S₁) ∧
    (IsSdEq p cad ((1 - p) / 2) (Set.Icc (p ^ 2 / (p - cad)) 1) ∧
      sdProfit p cad ((1 - p) / 2) (Set.Icc (p ^ 2 / (p - cad)) 1) = 0) := by sorry

end TargetGranularity.SdVsMd
