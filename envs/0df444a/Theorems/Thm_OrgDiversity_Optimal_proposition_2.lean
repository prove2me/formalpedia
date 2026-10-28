-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_proposition_2
-- name    : OrgDiversity.Optimal.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:08.678351+00:00
-- url     : https://prove2.me/theorems/f75f94d3-5a93-4aea-b19b-ddc1899f8e73
-- title:
--   Proposition 2, p. 24 — homogeneous organization optimal for α ≤ α_het; for α > α̂_het heterogeneous optimal iff k ≥ k(α)
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   Assume Assumptions 1–3:
--   - (A1) $\Gamma\ge F(b_H/2)/F(b_L/2)$;
--   - (A2) $\Gamma\ge\gamma$;
--   - (A3) $xf(x)$ is weakly increasing in $x>0$.
--
--   Let $\alpha_{hom}\in(1/2,1)$, $\alpha_{het}\in[1/2,1)$ and $\hat\alpha\in(1/2,1)$ solve
--   $$\alpha F(\alpha b_L)=(1-\alpha)F((1-\alpha)b_H)\Gamma,\qquad \alpha F(\alpha b_H)=(1-\alpha)F((1-\alpha)b_L)\Gamma,\qquad \alpha F(\alpha b_L)=(1-\alpha)F((1-\alpha)b_H),$$
--   respectively, and set $\hat\alpha_{het}=\max\{\alpha_{het},\hat\alpha\}$. Fix $\alpha\in(1/2,1]$. For each $k>0$ let $\pi_{hom}(\alpha,k),\pi_{het}(\alpha,k)$ be IM's optimal information efforts, and $V_{hom}(\alpha,k),V_{het}(\alpha,k)$ the principal's expected profits, i.e. the success probabilities under DM's optimal project choice and IM's optimal implementation and information effort.
--
--   **Proposition 2.**
--   1. If $\alpha\in(1/2,\alpha_{het}]$, then $V_{het}(\alpha,k)<V_{hom}(\alpha,k)$ for all $k>0$.
--   2. If $\alpha\in(\hat\alpha_{het},1]$, there is a threshold $k(\alpha)\in\big(0,\bar k_{het}(\alpha)\big)$ such that
--   $$V_{het}(\alpha,k)<V_{hom}(\alpha,k)\ \ (0<k<k(\alpha)),\qquad V_{het}(\alpha,k)\ge V_{hom}(\alpha,k)\ \ (k\ge k(\alpha)),$$
--   with strict inequality for $k\in\big(k(\alpha),\bar k_{hom}(\alpha)\big)$.
--
--   Here $\bar k_h(\alpha)$ is the least $k$ with $\pi_h(\alpha,k)=1$. This is the paper's main result: the homogeneous organization is strictly optimal when signals are weak. When signals are informative, preference diversity becomes optimal exactly when the information cost parameter $k$ is large. The reason is that IM in a heterogeneous organization works harder to gather information, to avoid ending up with his unfavourite default project.
--
--   **Formalization Note** The model objects are those of the definition `OrgDiversity.Optimal.Model`: $V_h(\alpha,k)$ is `successProb P h α (π_h k)`, where `π_h k` is any maximizer of IM's payoff on $[0,1]$ (`IsOptimalEffort`). The thresholds $\alpha_{hom},\alpha_{het},\hat\alpha$ are passed as roots of their defining equations together with the intervals the paper gives (`IsAlphaHom`, `IsAlphaHet`, `IsAlphaHat`). Each root is unique, so this matches the paper's "the solution". The over-barred thresholds are encoded through effort: $k<\bar k_h(\alpha)$, the minimum $k$ with $\pi_h(\alpha,k)=1$, is written $\pi_h(\alpha,k)<1$. The page writes $V_h(\alpha)$ in Proposition 2, omitting $k$; $V_h$ depends on $(\alpha,k)$, as in Lemmas A1–A3. \"For all $k<k(\alpha)$\" is read as $0<k<k(\alpha)$, since $k\in(0,\infty)$.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), p. 24, Proposition 2 (thresholds pp. 15, 16, 23–24)

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem proposition_2 (P : Params) (hP : P.Standing) (hA1 : P.Assumption1)
    (hA2 : P.Assumption2) (hA3 : P.Assumption3) (αhom αhet αhat : ℝ)
    (hhom : P.IsAlphaHom αhom) (hhet : P.IsAlphaHet αhet) (hhat : P.IsAlphaHat αhat)
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (πhom πhet : ℝ → ℝ)
    (hπhom : ∀ k : ℝ, 0 < k → IsOptimalEffort P .hom α k (πhom k))
    (hπhet : ∀ k : ℝ, 0 < k → IsOptimalEffort P .het α k (πhet k)) :
    (α ≤ αhet →
      ∀ k : ℝ, 0 < k → successProb P .het α (πhet k) < successProb P .hom α (πhom k)) ∧
    (max αhet αhat < α →
      ∃ kα : ℝ, 0 < kα ∧ πhet kα < 1 ∧
      (∀ k : ℝ, 0 < k → k < kα →
        successProb P .het α (πhet k) < successProb P .hom α (πhom k)) ∧
      (∀ k : ℝ, kα ≤ k → successProb P .hom α (πhom k) ≤ successProb P .het α (πhet k)) ∧
      (∀ k : ℝ, kα < k → πhom k < 1 →
        successProb P .hom α (πhom k) < successProb P .het α (πhet k))) := by sorry

end OrgDiversity.Optimal
