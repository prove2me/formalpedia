-- Prove2me | Theorems.Thm_PayAsBid_SoftReserve_proposition_1
-- name    : PayAsBid.SoftReserve.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:49.392748+00:00
-- url     : https://prove2.me/theorems/64e8665f-bc13-423a-add3-0f7aef46d7a0
-- title:
--   Proposition 1, p. 17 — every optimal equitable assortment mechanism is matched by a k-soft-reserve rule with s = b∗_L, r = b∗_H, same prices, same ECS
-- statement:
--   Consider the symmetric generalized affine demand model (Model 2) with $n$ suppliers, $\Theta_i=\{\theta_L,\theta_H\}$ and $f_i(\theta_L)=f_L$ for every $i$, under the standing assumptions. Let $q^*$ be an optimal equitable assortment mechanism with equilibrium prices $b^*_L,b^*_H$ and reserve price $r^*$, i.e. $(q^*,r^*,b^*_L,b^*_H)$ is an optimal solution of Problem (8). Then there is $k\in\{1,\dots,n\}$ such that the $k$-soft-reserve rule $q^{k,s,r}$ with soft reserve $s=b^*_L$ and hard reserve $r=b^*_H$:
--
--   1. is optimal, with the same equilibrium prices: $(q^{k,b^*_L,b^*_H},\,b^*_H,\,b^*_L,\,b^*_H)$ is an optimal solution of Problem (8);
--   2. yields the same expected consumer surplus:
--   $$ECS(q^{k,b^*_L,b^*_H},b^*_L,b^*_H)=ECS(q^*,b^*_L,b^*_H).$$
--
--   So, in the symmetric two-point setting, the search for an optimal equitable pay-as-bid mechanism can be restricted to the three-parameter family of $k$-soft reserves.
--
--   **Formalization Note.** Problem (8) is the paper's restriction of Problem (6)/(7) to symmetric pricing strategies (§4.2, p. 16). $k$ ranges over $1,\dots,n$; $k=n$ is the no-competition rule (p. 16), and when $b^*_L=b^*_H$ every $k$ gives it, so Definition 5's side condition $s<r$ is not imposed (p. 17 lists both optimal forms). The hypothesis is optimality, as on the page, not mere feasibility.
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), p. 17 (PDF 17), Proposition 1

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

namespace PayAsBid.SoftReserve

theorem proposition_1 {n : ℕ} (P : Params n) (hP : P.Standing)
    (q : AssortFn n) (r bL bH : ℝ) (hopt : IsOptimal8 P q r bL bH) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      IsOptimal8 P (kSR k bL bH) bH bL bH ∧
      ECS P (kSR k bL bH) bL bH = ECS P q bL bH := by sorry

end PayAsBid.SoftReserve
