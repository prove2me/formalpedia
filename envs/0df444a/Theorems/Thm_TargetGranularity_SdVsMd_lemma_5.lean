-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_lemma_5
-- name    : TargetGranularity.SdVsMd.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:57.653871+00:00
-- url     : https://prove2.me/theorems/5b5bd23c-6310-4184-bda0-8c0dc32f5dda
-- title:
--   Lemma 5, p. 40 (PDF 41), ε–δ form — the symmetric md profit for c_click just below c^max_click tends to 0 as c_ad → 0
-- statement:
--   Let $0<p<1$. For every $\varepsilon>0$ there is $\delta>0$ such that for every $c_{ad}\in(0,\delta)$ there is $\eta>0$ such that, for every click cost $c_{click}$ with
--   $$c^{max}_{click}(c_{ad},p)-\eta<c_{click}\le c^{max}_{click}(c_{ad},p),$$
--   every non-trivial symmetric md equilibrium earns profit $\Pi^{md}<\varepsilon$.
--
--   The page states this as: the limit $L(c_{ad},p)$ of $\Pi^{*md}$ as $c_{click}\to c^{max}_{click}(c_{ad},p)^-$ tends to $0$ as $c_{ad}\to0$. It is the md side of Proposition 3: near the threshold the md profit becomes negligible for small ad costs.
--
--   **Formalization Note** The page does not show that the one-sided limit $L$ exists, so the statement is the $\varepsilon$–$\delta$ bound that the proof of Proposition 3 uses, with the endpoint $c_{click}=c^{max}_{click}$ included (the proof of Lemma 5 discusses it). $c^{max}_{click}$ is the explicit Equation (7).
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), p. 40 (PDF 41), Lemma 5; proof, pp. 40–41 (PDF 41–42)

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Lemma 5, p. 40, in ε–δ form: for every `ε > 0` there is `δ > 0` such that for every
`c_ad ∈ (0, δ)` there is `η > 0` such that every non-trivial symmetric md equilibrium with
`c_click ∈ (c^max_click(c_ad, p) − η, c^max_click(c_ad, p)]` earns profit less than `ε`. -/
theorem lemma_5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ cad : ℝ, 0 < cad → cad < δ →
      ∃ η : ℝ, 0 < η ∧ ∀ cclick : ℝ, cmaxClick cad p - η < cclick →
        cclick ≤ cmaxClick cad p →
          ∀ S : Set (ℝ × ℝ), IsSymMdEq p cad cclick S → mdProfit p cad cclick S < ε := by sorry

end TargetGranularity.SdVsMd
