-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_lemma_6
-- name    : TargetGranularity.SdVsMd.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:56.106075+00:00
-- url     : https://prove2.me/theorems/49a50b8a-61e6-4097-88cd-6be64fe527f3
-- title:
--   Lemma 6, p. 41 (PDF 42) — for c_ad < min{p², p(1−p)}: (1−p)²/2 < c^max_click(c_ad, p) < (1−p)/2
-- statement:
--   Let $0<p<1$ and $0<c_{ad}<\min\{p^2,p(1-p)\}$, and let $c^{max}_{click}(c_{ad},p)$ be the threshold of Equation (7). Then
--   $$\frac{(1-p)^2}{2}<c^{max}_{click}(c_{ad},p)<\frac{1-p}{2}.$$
--
--   In this range Equation (7) is in its third case, $\frac{c_{ad}^2-3c_{ad}(1-p)p+3(1-p)^2p^2}{6p(p(1-p)(1+p)-c_{ad})}$. The lemma places the md existence threshold inside the interval of click costs on which Lemma 4 controls the sd profit, which is how Lemmas 4 and 5 combine into Proposition 3.
--
--   **Formalization Note** $c_{ad}>0$ is the model's standing assumption (p. 10). All denominators of the third case are positive in this range.
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), p. 41 (PDF 42), Lemma 6

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Lemma 6, p. 41: for `0 < c_ad < min{p², p(1 − p)}`,
`(1 − p)²/2 < c^max_click(c_ad, p) < (1 − p)/2`. -/
theorem lemma_6 (p cad : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcad : 0 < cad)
    (hcadp2 : cad < p ^ 2) (hcadp1 : cad < p * (1 - p)) :
    (1 - p) ^ 2 / 2 < cmaxClick cad p ∧ cmaxClick cad p < (1 - p) / 2 := by sorry

end TargetGranularity.SdVsMd
