-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_kl_display
-- name    : UniformDRO.LowerBound.kl_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:53.252973+00:00
-- url     : https://prove2.me/theorems/87b7fbb6-e48c-4ee7-bdca-46e956cc0287
-- title:
--   Proof of Thm 3 (App. D.1), p. 46 — for δ ≤ ½(1 − p_k), D_kl(P₂‖P₁) ≤ 8δ²/(p_k(1 − p_k))
-- statement:
--   Let $k > 1$, $\rho > 0$ and $p_k = (1 + k(k-1)\rho)^{-1/(k-1)} \in (0,1)$. For $0 < \delta \le p_k$ with $\delta \le \tfrac12(1 - p_k)$, let $P_1$ and $P_2$ be the laws on $\{0, M\}$ with masses $p_k + \delta$ and $p_k - \delta$ at $M$. Then
--   $$D_{\mathrm{kl}}(P_2\|P_1) = (1 - p_k + \delta)\log\frac{1 - p_k + \delta}{1 - p_k - \delta} + (p_k - \delta)\log\frac{p_k - \delta}{p_k + \delta} \le \frac{8\delta^2}{p_k(1-p_k)} .$$
--
--   This controls the information in one observation for distinguishing the two laws of the $n^{-1/2}$ branch of Theorem 3.
--
--   **Formalization Note.** $D_{\mathrm{kl}}$ between two laws on two points is the platform's Bernoulli relative entropy $d(p,q) = p\log(p/q) + (1-p)\log((1-p)/(1-q))$, evaluated at $p = p_k - \delta$, $q = p_k + \delta \in (0,1)$; it is the page's middle expression with the two terms in the other order. The hypothesis $\delta \le p_k$ is not repeated in the display's sentence but is the standing range $0 < \delta \le p_k \wedge (1-p_k)$ of p. 45; it keeps $p_k - \delta$ a probability.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 3 (App. D.1), p. 46, KL display; range of δ from p. 45

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem kl_display (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ)
    (hδp : δ ≤ pk k ρ) (hδq : δ ≤ (1 - pk k ρ) / 2) :
    BanditAlgorithm.bernoulliRelativeEntropy (pk k ρ - δ) (pk k ρ + δ) ≤
      8 * δ ^ 2 / (pk k ρ * (1 - pk k ρ)) := by sorry

end UniformDRO.LowerBound
