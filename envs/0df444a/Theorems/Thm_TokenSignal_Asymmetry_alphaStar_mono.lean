-- Prove2me | Theorems.Thm_TokenSignal_Asymmetry_alphaStar_mono
-- name    : TokenSignal.Asymmetry.alphaStar_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:59.014181+00:00
-- url     : https://prove2.me/theorems/e9ba93f6-2c2a-4149-a097-d6a077d6f982
-- title:
--   Threshold increases with low-type mean and volatility
-- statement:
--   Holding the other parameters fixed, $\alpha^*$ is strictly increasing as the low-type mean $\mu_L$ increases below $\mu_H$, and strictly increasing as the standard deviation $\sigma$ increases above zero:
--
--   $$\mu_L' < \mu_L'' < \mu_H\implies\alpha^*(\mu_L')<\alpha^*(\mu_L''),\qquad 0<\sigma'<\sigma''\implies\alpha^*(\sigma')<\alpha^*(\sigma'').$$
--
--   These monotonicities are the comparative statics stated in the proof of Proposition 6.
--
--   **Formalization Note** Strict monotonicity is the global form of the paper’s positive-derivative assertions.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 32 (PDF 33), proof of Proposition 6

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

namespace TokenSignal.Asymmetry

theorem alphaStar_mono (P : Params) (hS : P.Standing) :
    StrictMonoOn (fun μL' : ℝ => αStar { P with μL := μL' }) (Set.Iio P.μH) ∧
    StrictMonoOn (fun σ' : ℝ => αStar { P with σ := σ' }) (Set.Ioi 0) := by sorry
end TokenSignal.Asymmetry
