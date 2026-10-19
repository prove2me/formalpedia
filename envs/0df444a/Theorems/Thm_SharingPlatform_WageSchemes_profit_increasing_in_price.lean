-- Prove2me | Theorems.Thm_SharingPlatform_WageSchemes_profit_increasing_in_price
-- name    : SharingPlatform.WageSchemes.profit_increasing_in_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:56.961893+00:00
-- url     : https://prove2.me/theorems/7c81e635-704a-45c6-bbc8-3dcded3189dd
-- title:
--   Proof of Proposition 3, A.8, pp. 51–52 (PDF 52–53) — equilibrium profit (66) increases in the equilibrium price below p̂, and all three equilibrium prices lie below p̂
-- statement:
--   When demand equals supply, $-k + m w^* = a - c p^*$, so an equilibrium profit can be written as a function of the equilibrium price alone:
--
--   $$\Pi(p) = \left(\frac{m+c}{m}\,p - \frac{a+k}{m}\right)(a - c p).$$
--
--   Let $\hat p = \frac{(m+c)a + c(a+k)}{2c(m+c)}$, the point where $\Pi'(p) = \frac{(m+c)a}{m} + \frac{c(a+k)}{m} - \frac{2c(m+c)p}{m}$ vanishes. Under the standing assumptions:
--   1. $\Pi$ is strictly increasing on $(-\infty, \hat p]$;
--   2. the DCR price satisfies $p^{D*} < \hat p$, and the FW price satisfies $p^{W*} < \hat p$;
--   3. for every $\alpha \in (\bar\alpha, 1)$ with $f(\alpha) = 0$, the FCR price satisfies $\frac{a+k}{c+m(1-\alpha)} < \hat p$.
--
--   Consequently the ranking of the three equilibrium profits is the ranking of the three equilibrium prices.
--
--   **Formalization Note** $p^{D*}$, $p^{W*}$, $\bar\alpha$ and $f$ are the closed forms (4), (9), (39), (44) of the definition file. The paper derives part 2 from its proof of Proposition 2(c) (pp. 50–51).
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, proof of Proposition 3, A.8, pp. 51–52 (PDF 52–53); proof of Proposition 2(c), A.7, p. 51 (PDF 52), Equations (66)–(68)

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

theorem profit_increasing_in_price (P : Params) (hP : P.Standing) :
    StrictMonoOn (profitAtPrice P) (Set.Iic (pHat P)) ∧
    pD P < pHat P ∧ pW P < pHat P ∧
    ∀ α : ℝ, α ∈ Set.Ioo (alphaBar P) 1 → fFCR P α = 0 → priceFCR P α < pHat P := by sorry
end SharingPlatform.WageSchemes
