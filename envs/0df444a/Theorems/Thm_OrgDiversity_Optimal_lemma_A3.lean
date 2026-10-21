-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_lemma_A3
-- name    : OrgDiversity.Optimal.lemma_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:00.479239+00:00
-- url     : https://prove2.me/theorems/201ad89f-ac6e-4a38-b171-7afdb3fbe46d
-- title:
--   Lemma A3, p. 46 — for α ∈ (α̂_het, α_hom] a threshold k(α) ∈ (0, k̄^R_het(α)) separates the optimal organizations
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   Assume Assumptions 1–3. Let $\alpha_{hom},\alpha_{het}$ be the thresholds of Lemma 1 and $\hat\alpha\in(1/2,1)$ the solution of $\alpha F(\alpha b_L)=(1-\alpha)F((1-\alpha)b_H)$, and set $\hat\alpha_{het}=\max\{\alpha_{het},\hat\alpha\}$. Let $\alpha\in(\hat\alpha_{het},\alpha_{hom}]$ (DM non-reactive in the homogeneous, reactive in the heterogeneous organization), and let $\pi_{hom}(\alpha,k),\pi_{het}(\alpha,k)$ be IM's optimal information efforts and $V_h(\alpha,k)$ the resulting success probabilities.
--
--   **Lemma A3.** there is $k(\alpha)\in\big(0,\bar k^R_{het}(\alpha)\big)$ such that
--   1. $V_{het}(\alpha,k)<V_{hom}(\alpha,k)$ for all $0<k<k(\alpha)$;
--   2. $V_{het}(\alpha,k)\ge V_{hom}(\alpha,k)$ for all $k\ge k(\alpha)$;
--   3. $V_{het}(\alpha,k)>V_{hom}(\alpha,k)$ for all $k\in\big(k(\alpha),\bar k^{N}_{hom}(\alpha)\big)$.
--
--   Here $\bar k^N_{hom}(\alpha)$ is the least $k$ with $\pi^N_{hom}(\alpha,k)=1$. With Lemma A2 this gives Case 2 of Proposition 2.
--
--   **Formalization Note** The model objects are those of the definition `OrgDiversity.Optimal.Model`: $V_h(\alpha,k)$ is `successProb P h α (π_h k)`, where `π_h k` is any maximizer of IM's payoff on $[0,1]$ (`IsOptimalEffort`). The thresholds $\alpha_{hom},\alpha_{het},\hat\alpha$ are passed as roots of their defining equations together with the intervals the paper gives (`IsAlphaHom`, `IsAlphaHet`, `IsAlphaHat`). Each root is unique, so this matches the paper's "the solution". The over-barred thresholds are encoded through effort: $k<\bar k_h(\alpha)$, the minimum $k$ with $\pi_h(\alpha,k)=1$, is written $\pi_h(\alpha,k)<1$.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), p. 46, Lemma A3 (α̂ defined p. 23, α̂_het p. 24)

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem lemma_A3 (P : Params) (hP : P.Standing) (hA1 : P.Assumption1) (hA2 : P.Assumption2)
    (hA3 : P.Assumption3) (αhom αhet αhat : ℝ) (hhom : P.IsAlphaHom αhom)
    (hhet : P.IsAlphaHet αhet) (hhat : P.IsAlphaHat αhat)
    (α : ℝ) (hα : max αhet αhat < α) (hα1 : α ≤ αhom)
    (πhom πhet : ℝ → ℝ)
    (hπhom : ∀ k : ℝ, 0 < k → IsOptimalEffort P .hom α k (πhom k))
    (hπhet : ∀ k : ℝ, 0 < k → IsOptimalEffort P .het α k (πhet k)) :
    ∃ kα : ℝ, 0 < kα ∧ πhet kα < 1 ∧
      (∀ k : ℝ, 0 < k → k < kα →
        successProb P .het α (πhet k) < successProb P .hom α (πhom k)) ∧
      (∀ k : ℝ, kα ≤ k → successProb P .hom α (πhom k) ≤ successProb P .het α (πhet k)) ∧
      (∀ k : ℝ, kα < k → πhom k < 1 →
        successProb P .hom α (πhom k) < successProb P .het α (πhet k)) := by sorry

end OrgDiversity.Optimal
