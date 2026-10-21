-- Prove2me | Theorems.Thm_RefurbCommit_DefectProfit_proposition_3
-- name    : RefurbCommit.DefectProfit.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:58.080861+00:00
-- url     : https://prove2.me/theorems/15bd6216-f169-4a46-9e37-7ef7d8202da2
-- title:
--   Proposition 3, p. 14 (PDF 15) — Π^C decreases in α; Π* ≤ Π^C, with equality for α ≥ αc; at the Figure 3 parameters Π* is non-monotone in α
-- statement:
--   **Proposition 3 (Defect rate, time inconsistency problem, and firm profit).** Fix parameters satisfying the standing assumptions, and let $\Pi^*(\alpha)$ and $\Pi^C(\alpha)$ be the firm's two-period profits without and with commitment.
--
--   1. $\Pi^C$ is strictly decreasing in the defect rate on $\{\alpha>0:\Pi^C(\alpha)>0\}$.
--   2. $\Pi^*(\alpha)\le\Pi^C(\alpha)$ for every $\alpha>0$, and
--      - (a) with $\alpha_c=(v_n-c_n)/(c_n+h)$, $\Pi^*(\alpha)=\Pi^C(\alpha)$ for every $\alpha\ge\alpha_c$, $\alpha>0$;
--      - (b) at the Figure 3 parameters ($c_n=0.7$, $c_r=0.1$, $v_n=1$, $\rho=0.9$, $k_r=0.25$, $h=0.05$) there is $\hat v_r<v_n=1$ such that for every $v_r\in(\hat v_r,1)$ the profit $\alpha\mapsto\Pi^*(\alpha)$ is neither nondecreasing nor nonincreasing on $(0,\infty)$:
--   $$\exists\,\hat v_r<1\ \ \forall v_r\in(\hat v_r,1):\quad \Pi^*\ \text{is not monotone on}\ (0,\infty).$$
--
--   The result says that defective returns, which only add cost under commitment, can raise the profit of a firm that cannot commit: refurbished returns displace the firm's own future new-product sales and so act as a commitment device.
--
--   **Formalization Note** Part (i) is read as strict decrease on the paper's positive-profit region. Part (ii)(a) uses the explicit threshold $\alpha_c$ of the proof (p. A-5). Part (ii)(b) is a pinned-down version: as printed, "there exists $\hat v_r$ such that $\Pi^*$ is non-monotonic when $\hat v_r<v_r<v_n$" holds trivially with $\hat v_r=v_n$; the paper's $\hat v_r=\max\{\hat v_{r1},\hat v_{r2}\}$ leaves $\hat v_{r1}$ unspecified, and Appendix C concedes that $\hat v_r<v_n$ cannot be guaranteed in general. The statement therefore fixes the other parameters at the paper's Figure 3 values and requires $\hat v_r<v_n$. "Non-monotonic" means neither monotone nor antitone on $\alpha>0$. The paper's bound $h<\bar h$ (p. 8) is not imposed; at the Figure 3 parameters with $v_r$ close to $1$ it would exclude the defect rates where profit rises.
-- source:
--   Singh, Ramachandran & Subramanian, Intertemporal product management with strategic consumers: the value of defective product returns, accepted manuscript (MSOM, Dec. 2020; SSRN 2511424), p. 14 (PDF 15), Proposition 3; proof pp. A-4–A-6 (PDF 37–39); Figure 3 parameters p. 15 (PDF 16)

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

namespace RefurbCommit.DefectProfit

/-- Proposition 3 (p. 14). Parts (i), (ii), (ii)(a) for every parameter vector satisfying
the standing assumptions (αc explicit, p. A-5); part (ii)(b) at the Figure 3 parameters
(p. 15), with the threshold `v̂r` required to lie below `vn = 1`. -/
theorem proposition_3 (P : Params) (hP : P.Standing) :
    -- (i)
    StrictAntiOn (PiC P) {α | 0 < α ∧ 0 < PiC P α} ∧
    -- (ii)
    (∀ α, 0 < α → PiStar P α ≤ PiC P α) ∧
    -- (ii)(a)
    (∀ α, 0 < α → alphaC P ≤ α → PiStar P α = PiC P α) ∧
    -- (ii)(b), at the Figure 3 parameters
    (∃ vhat : ℝ, vhat < 1 ∧ ∀ vr, vhat < vr → vr < 1 →
      ¬ MonotoneOn (PiStar (fig3 vr)) (Set.Ioi 0) ∧
      ¬ AntitoneOn (PiStar (fig3 vr)) (Set.Ioi 0)) := by sorry

end RefurbCommit.DefectProfit
