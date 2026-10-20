-- Prove2me | Theorems.Thm_SharingPlatform_WageSchemes_fcr_vs_fw
-- name    : SharingPlatform.WageSchemes.fcr_vs_fw
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:02.651999+00:00
-- url     : https://prove2.me/theorems/4d0cb887-985e-4887-89e0-07805df853ec
-- title:
--   Proof of Proposition 3, A.8, pp. 52–53 (PDF 53–54) — α^{W*} < α^{F*} iff cl − bm > 0, and p^{W*} < p^{F*} iff α^{W*} < α^{F*}
-- statement:
--   Assume the standing assumptions. Let $w^{W*}$, $p^{W*}$ be the FW equilibrium wage (8) and price (9), and let $\alpha^{W*} = 1 - w^{W*}/p^{W*}$ be the commission rate they imply. Let $\alpha \in (\bar\alpha, 1)$ be a zero of $f$ (the FCR commission rate of Lemma 2), with FCR price $p^F(\alpha) = \frac{a+k}{c+m(1-\alpha)}$. Then:
--   1. $\alpha^{W*} < \alpha$ if and only if $bm < cl$;
--   2. $\alpha < \alpha^{W*}$ if and only if $cl < bm$;
--   3. $p^{W*} < p^F(\alpha)$ if and only if $\alpha^{W*} < \alpha$.
--
--   With the monotonicity of profit in price, this orders the FW and FCR profits by the sign of $cl - bm$.
--
--   **Formalization Note** The page displays $\alpha^{W*}$ as a closed form in which $k$ appears with the wrong sign throughout. The statement uses the definition $\alpha^{W*} = 1 - w^{W*}/p^{W*}$, which is what the page means.
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, proof of Proposition 3, A.8, pp. 52–53 (PDF 53–54), comparison of FCR and FW

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

theorem fcr_vs_fw (P : Params) (hP : P.Standing)
    (α : ℝ) (hα : α ∈ Set.Ioo (alphaBar P) 1) (hf : fFCR P α = 0) :
    (alphaW P < α ↔ P.b * P.m < P.c * P.l) ∧
    (α < alphaW P ↔ P.c * P.l < P.b * P.m) ∧
    (pW P < priceFCR P α ↔ alphaW P < α) := by sorry
end SharingPlatform.WageSchemes
