-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_success_prob_closed_form
-- name    : OrgDiversity.Optimal.success_prob_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:05.386153+00:00
-- url     : https://prove2.me/theorems/cc2d1580-91ab-4dba-b143-dd9b25c49cfb
-- title:
--   Appendix A3, p. 45 — closed forms of the success probabilities V_hom and V_het
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   Assume Assumption 1, let $\alpha_{hom},\alpha_{het}$ be the thresholds of Lemma 1, $\alpha\in(1/2,1]$, $k>0$, and let $\pi_{hom}$ and $\pi_{het}$ be optimal information efforts in the respective organizations at $(\alpha,k)$. The success probability of the homogeneous organization equals
--   $$V_{hom}=\begin{cases}\tfrac12\Big(F(\tfrac{b_H}{2})+\pi_{hom}\big[\alpha F(\alpha b_H)+(1-\alpha)F((1-\alpha)b_H)-F(\tfrac{b_H}{2})\big]\Big),&\alpha\le\alpha_{hom},\\[2pt] \tfrac12\Big(F(\tfrac{b_H}{2})+\pi_{hom}\big[\alpha F(\alpha b_H)+\alpha F(\alpha b_L)-F(\tfrac{b_H}{2})\big]\Big),&\alpha>\alpha_{hom},\end{cases}$$
--   and that of the heterogeneous organization equals
--   $$V_{het}=\begin{cases}\tfrac12\Big(F(\tfrac{b_L}{2})+\pi_{het}\big[\alpha F(\alpha b_L)+(1-\alpha)F((1-\alpha)b_L)-F(\tfrac{b_L}{2})\big]\Big),&\alpha\le\alpha_{het},\\[2pt] \tfrac12\Big(F(\tfrac{b_L}{2})+\pi_{het}\big[\alpha F(\alpha b_L)+\alpha F(\alpha b_H)-F(\tfrac{b_L}{2})\big]\Big),&\alpha>\alpha_{het}.\end{cases}$$
--
--   These are the paper's $V_{hom}(\alpha,k)$ and $V_{het}(\alpha,k)$, the formulas on which Lemmas A1–A3 rest.
--
--   **Formalization Note** The efforts are any maximizers of IM's payoff over $[0,1]$; the Appendix writes them as $\pi^N_h(\alpha,k)$ or $\pi^R_h(\alpha,k)$. Only Assumption 1 is assumed for this algebraic identity, as in the derivation through Lemma 1.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), p. 45, Appendix A3 (unnumbered display of V_hom(α, k) and V_het(α, k))

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem success_prob_closed_form (P : Params) (hP : P.Standing) (hA1 : P.Assumption1)
    (αhom αhet : ℝ) (hhom : P.IsAlphaHom αhom) (hhet : P.IsAlphaHet αhet)
    (α k : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1) (hk : 0 < k)
    (πhom πhet : ℝ)
    (hπhom : IsOptimalEffort P .hom α k πhom)
    (hπhet : IsOptimalEffort P .het α k πhet) :
    successProb P .hom α πhom =
      (if α ≤ αhom then
        (1 / 2) * (P.F (P.bH / 2) + πhom * (α * P.F (α * P.bH) +
          (1 - α) * P.F ((1 - α) * P.bH) - P.F (P.bH / 2)))
      else
        (1 / 2) * (P.F (P.bH / 2) + πhom * (α * P.F (α * P.bH) + α * P.F (α * P.bL) -
          P.F (P.bH / 2)))) ∧
    successProb P .het α πhet =
      (if α ≤ αhet then
        (1 / 2) * (P.F (P.bL / 2) + πhet * (α * P.F (α * P.bL) +
          (1 - α) * P.F ((1 - α) * P.bL) - P.F (P.bL / 2)))
      else
        (1 / 2) * (P.F (P.bL / 2) + πhet * (α * P.F (α * P.bL) + α * P.F (α * P.bH) -
          P.F (P.bL / 2)))) := by sorry

end OrgDiversity.Optimal
