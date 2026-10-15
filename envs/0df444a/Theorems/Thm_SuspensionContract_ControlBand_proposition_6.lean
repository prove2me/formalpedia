-- Prove2me | Theorems.Thm_SuspensionContract_ControlBand_proposition_6
-- name    : SuspensionContract.ControlBand.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:15.164756+00:00
-- url     : https://prove2.me/theorems/cef5e890-7dab-442d-b604-88d5e572e6e6
-- title:
--   Proposition 6, p. 26 — under Condition 3 there are (𝖼, 𝐰̂, ϑ̄, ϑ̲) with 𝖼 > 0, ϑ̲ < ϑ̄ < 𝐰̂ satisfying value matching and smooth pasting (42)–(45) and ϑ̄ > w̌(𝐰̂)
-- statement:
--   Assume the standing assumptions and Condition 3. Then there exist parameters $(\mathsf c,\hat{\mathbf w},\bar\vartheta,\underline\vartheta)$ with $\mathsf c>0$ and $0<\underline\vartheta<\bar\vartheta<\hat{\mathbf w}$, where $\hat{\mathbf w}<\hat{\mathrm w}$ (Lemma 3) in the Condition 1 case and $\hat{\mathbf w}<\bar w$ in the Condition 2 case, such that
--   $$\mathcal V_{\hat{\mathbf w}}(\underline\vartheta)=V_{\mathsf c}(\underline\vartheta),\ (42)\qquad \mathcal V_{\hat{\mathbf w}}'(\underline\vartheta)=V_{\mathsf c}'(\underline\vartheta),\ (43)$$
--   $$\mathcal V_{\hat{\mathbf w}}(\bar\vartheta)=V_{\mathsf c}(\bar\vartheta)+K,\ (44)\qquad \mathcal V_{\hat{\mathbf w}}'(\bar\vartheta)=V_{\mathsf c}'(\bar\vartheta)>1,\ (45)$$
--   and $\bar\vartheta>\check w(\hat{\mathbf w})$.
--
--   The tuple gives the control-band value functions (46): suspension below $\underline\vartheta$ and value matching/smooth pasting at both ends of the band.
--
--   **Formalization Note.** The page prints $\hat{\mathbf w}<\hat{\mathrm w}$ for both cases, but $\hat{\mathrm w}$ exists only under Condition 1; the proof for Condition 2 concludes $\hat{\mathbf w}<\bar w$, which is what is stated there. $0<\underline\vartheta$ is added (the proof's $\underline\vartheta$ lies in $(0,\underline\theta^0)$ or $(\breve{\underline\theta},\underline\theta^0)$ with $\breve{\underline\theta}>0$).
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 26, Proposition 6, (42)–(45); proof EC.3.9, pp. ec34–ec40

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds
import Definitions.Def_SuspensionContract_ControlBand_Construction

namespace SuspensionContract.ControlBand

theorem proposition_6 (P : Params) (hP : P.Standing) (h3 : P.Condition3) :
    ∃ c wB thHi thLo : ℝ, P.Prop6Params c wB thHi thLo := by sorry

end SuspensionContract.ControlBand
