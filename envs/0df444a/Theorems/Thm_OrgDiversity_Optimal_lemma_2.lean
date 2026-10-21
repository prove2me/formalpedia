-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_lemma_2
-- name    : OrgDiversity.Optimal.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:58.34513+00:00
-- url     : https://prove2.me/theorems/dc18e49c-c4cf-4eaf-9d82-3699ad2bd350
-- title:
--   Lemma 2, p. 19 — π^R_hom(α, k) > 0 for α ∈ (α_hom, 1] and k > 0
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   **Lemma 2.** Under Assumptions 1 and 2, let $\alpha_{hom}$ be the threshold of Lemma 1. For every $\alpha\in(\alpha_{hom},1]$ and every $k>0$,
--   $$\pi^R_{hom}(\alpha,k)=\min\Big\{k\Big(\tfrac12K(\alpha b_H)+\tfrac12K(\alpha b_L)-K\big(\tfrac{b_H}{2}\big)\Big),1\Big\}>0,$$
--   where $K(x)=\int_0^xF(c)\,dc$.
--
--   So when DM is reactive in the homogeneous organization, IM still has a strictly positive incentive to gather information.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), p. 19, Lemma 2

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem lemma_2 (P : Params) (hP : P.Standing) (hA1 : P.Assumption1) (hA2 : P.Assumption2)
    (αhom : ℝ) (hhom : P.IsAlphaHom αhom) (α : ℝ) (hα : αhom < α) (hα1 : α ≤ 1)
    (k : ℝ) (hk : 0 < k) :
    0 < min (k * mbRhom P α) 1 := by sorry

end OrgDiversity.Optimal
