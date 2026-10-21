-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_lemma_A1
-- name    : OrgDiversity.Optimal.lemma_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:57.725308+00:00
-- url     : https://prove2.me/theorems/58216544-3cba-4484-9ad1-448445867a30
-- title:
--   Lemma A1, p. 46 — V_het(α, k) < V_hom(α, k) for α ∈ (1/2, α_het] and all k > 0
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   Assume Assumptions 1–3. Let $\alpha_{het}$ be the threshold of Lemma 1, $\alpha\in(1/2,\alpha_{het}]$, and let $\pi_{hom}(\alpha,k)$ and $\pi_{het}(\alpha,k)$ be IM's optimal information efforts. Write $V_h(\alpha,k)$ for the success probability of organization $h$ under DM's optimal choice and IM's optimal effort.
--
--   **Lemma A1.** For every $k>0$,
--   $$V_{het}(\alpha,k)<V_{hom}(\alpha,k).$$
--
--   This is Case 1 of Proposition 2: when the signal is too weak for DM to react to in either organization, the homogeneous organization is strictly better for the principal.
--
--   **Formalization Note** The model objects are those of the definition `OrgDiversity.Optimal.Model`: $V_h(\alpha,k)$ is `successProb P h α (π_h k)`, where `π_h k` is any maximizer of IM's payoff on $[0,1]$ (`IsOptimalEffort`). The thresholds $\alpha_{hom},\alpha_{het},\hat\alpha$ are passed as roots of their defining equations together with the intervals the paper gives (`IsAlphaHom`, `IsAlphaHet`, `IsAlphaHat`). Each root is unique, so this matches the paper's "the solution". The over-barred thresholds are encoded through effort: $k<\bar k_h(\alpha)$, the minimum $k$ with $\pi_h(\alpha,k)=1$, is written $\pi_h(\alpha,k)<1$.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), p. 46, Lemma A1

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem lemma_A1 (P : Params) (hP : P.Standing) (hA1 : P.Assumption1) (hA2 : P.Assumption2)
    (hA3 : P.Assumption3) (αhet : ℝ) (hhet : P.IsAlphaHet αhet)
    (α : ℝ) (hα : 1 / 2 < α) (hαhet : α ≤ αhet)
    (πhom πhet : ℝ → ℝ)
    (hπhom : ∀ k : ℝ, 0 < k → IsOptimalEffort P .hom α k (πhom k))
    (hπhet : ∀ k : ℝ, 0 < k → IsOptimalEffort P .het α k (πhet k)) :
    ∀ k : ℝ, 0 < k → successProb P .het α (πhet k) < successProb P .hom α (πhom k) := by sorry

end OrgDiversity.Optimal
