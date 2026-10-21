-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_proposition_1
-- name    : OrgDiversity.Optimal.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:04.396982+00:00
-- url     : https://prove2.me/theorems/b78f0a7b-2c90-4c9d-a21d-099f4ab34897
-- title:
--   Proposition 1, p. 20 — π_hom ≥ π_het for α ≤ α_het (Assumption 3), π_hom ≤ π_het for α > α_het
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   Assume Assumptions 1 and 2, let $\alpha_{hom},\alpha_{het}$ be the thresholds of Lemma 1, and $\alpha\in(1/2,1]$. Let $\pi_{hom}(\alpha,k)$ and $\pi_{het}(\alpha,k)$ be IM's optimal information efforts in the two organizations, for every $k>0$.
--
--   **Proposition 1.**
--   1. If $\alpha\le\alpha_{het}$ and Assumption 3 holds ($xf(x)$ weakly increasing on $x>0$), then for every $k>0$, $\pi_{hom}(\alpha,k)\ge\pi_{het}(\alpha,k)$, strictly if $k<\bar k_{het}(\alpha)$.
--   2. If $\alpha>\alpha_{het}$, then for every $k>0$, $\pi_{hom}(\alpha,k)\le\pi_{het}(\alpha,k)$, strictly if $k<\bar k_{hom}(\alpha)$.
--
--   Here $\bar k_h(\alpha)$ is the least $k$ with $\pi_h(\alpha,k)=1$. For weak signals IM gathers more information when DM's default project is his favourite, and for strong signals he gathers more in the heterogeneous organization (the "ignorance-avoiding effect").
--
--   **Formalization Note** "$k<\bar k_h(\alpha)$" is written $\pi_h(\alpha,k)<1$. The efforts are arbitrary maximizers of IM's payoff on $[0,1]$, given as functions of $k$.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), p. 20, Proposition 1

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem proposition_1 (P : Params) (hP : P.Standing) (hA1 : P.Assumption1)
    (hA2 : P.Assumption2) (αhom αhet : ℝ) (hhom : P.IsAlphaHom αhom)
    (hhet : P.IsAlphaHet αhet) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (πhom πhet : ℝ → ℝ)
    (hπhom : ∀ k : ℝ, 0 < k → IsOptimalEffort P .hom α k (πhom k))
    (hπhet : ∀ k : ℝ, 0 < k → IsOptimalEffort P .het α k (πhet k)) :
    (α ≤ αhet → P.Assumption3 →
      ∀ k : ℝ, 0 < k → πhet k ≤ πhom k ∧ (πhet k < 1 → πhet k < πhom k)) ∧
    (αhet < α →
      ∀ k : ℝ, 0 < k → πhom k ≤ πhet k ∧ (πhom k < 1 → πhom k < πhet k)) := by sorry

end OrgDiversity.Optimal
