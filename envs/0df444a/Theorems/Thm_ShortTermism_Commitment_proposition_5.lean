-- Prove2me | Theorems.Thm_ShortTermism_Commitment_proposition_5
-- name    : ShortTermism.Commitment.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:17.676987+00:00
-- url     : https://prove2.me/theorems/f6f5d01e-4c84-4ac5-b530-69090d3d4f7d
-- title:
--   Proposition 5, p. 19 — f solves the no-underinvestment problem (A.29) iff it solves the no-overhang problem (A.27)
-- statement:
--   In the setting of the mission's model, assume the standing assumptions, fix a coupon $C$, let $f_u$ be the unlevered value solving (25) with the conditions of Proposition 3, and let $(a_u,e_u)$ be its effort policy: for every $\delta\ge\underline\delta$ the pair $(a_u(\delta),e_u(\delta))$ lies in $[0,\bar a]\times[0,\bar e]$ and maximizes over that box the braces of the unlevered HJB (25),
--   $$\delta(\psi+e)-\tfrac12(\theta_aa^2+2\theta_{ae}ae+\theta_ee^2)\delta+(\phi+a)\delta f_u'(\delta)+\tfrac12\sigma_\delta^2\delta^2f_u''(\delta)-\frac{\gamma r\delta^2}{2}\Sigma(a,e).$$
--   Then for every function $f$ and every threshold $\delta_B$,
--   $$(f,\delta_B)\ \text{solves the no-underinvestment problem (A.29)}\iff(f,\delta_B)\ \text{solves the no-overhang problem (A.27)}.$$
--   Here (A.27) requires $rf(\delta)=H_C(\delta,a_u(\delta),e_u(\delta),f'(\delta),f''(\delta))$ for $\delta>\delta_B$, while (A.29) requires $rf(\delta)=\max_{e\in[0,\bar e]}H_C(\delta,a_u(\delta),e,f'(\delta),f''(\delta))$ for $\delta>\delta_B$; both include value matching $f(\delta_B)=0$, smooth pasting $f'(\delta_B)=0$ and transversality $f'(\delta)\to\psi/(r-\phi)$.
--
--   In words: if shareholders commit to the unlevered long-term-effort policy $a_u$, they find it optimal to implement the unlevered short-term-effort policy $e_u$ as well, so commitment to $a_u$ alone delivers the no-debt-overhang outcome and debt causes no excessive short-termism beyond what it induces through long-term effort.
--
--   **Formalization Note** The unlevered value hypothesis records (25), $f_u(0)=0$, and the smoothness and linear growth of Proposition 3. The effort box $[0,\bar a]\times[0,\bar e]$ for $(a_u,e_u)$ comes from Definition 1 and Appendix A.2.1; without it $e_u(\delta)$ could leave $[0,\bar e]$ and the equivalence would fail. The same $f$ and the same $\delta_B$ appear on both sides, as in the paper's proof ("$\delta_B^{NO}=\delta_B^{NU}$"). The added standing assumption $\phi<r$ makes $\psi/(r-\phi)$ well defined.
-- source:
--   Hackbarth, Rivera & Wong, Optimal Short-Termism, ECGI Finance Working Paper 546/2018 (June 2021 version, SSRN 3060869), p. 19 (PDF 23), Proposition 5; problems (A.27), (A.29) of Appendix A.4.3, pp. 49–50 (PDF 53–54)

import Mathlib
import Definitions.Def_ShortTermism_Commitment_Model

namespace ShortTermism.Commitment

theorem proposition_5 (P : Params) (hP : P.Standing) (C : ℝ)
    (fu au eu : ℝ → ℝ) (hv : IsUnleveredValue P fu) (hu : IsUnleveredPolicy P fu au eu)
    (f : ℝ → ℝ) (dB : ℝ) :
    SolvesNU P C au f dB ↔ SolvesNO P C au eu f dB := by sorry

end ShortTermism.Commitment
