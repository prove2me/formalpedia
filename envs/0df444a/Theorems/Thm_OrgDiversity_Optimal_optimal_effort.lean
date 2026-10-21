-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_optimal_effort
-- name    : OrgDiversity.Optimal.optimal_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:56.98559+00:00
-- url     : https://prove2.me/theorems/14a3f999-004a-446c-b49c-7af8e9d99cbb
-- title:
--   §3.3, pp. 18–20 — IM's optimal information effort is min{k · (marginal benefit), 1}
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   Assume Assumptions 1 and 2, let $\alpha_{hom}$ and $\alpha_{het}$ be the thresholds of Lemma 1, $\alpha\in(1/2,1]$ and $k>0$. Then $\pi\in[0,1]$ maximizes IM's ex ante payoff in the homogeneous organization if and only if
--   $$\pi=\pi_{hom}(\alpha,k)=\begin{cases}\min\big\{k\big(\tfrac12K(\alpha b_H)+\tfrac12K((1-\alpha)b_H)-K(\tfrac{b_H}{2})\big),1\big\}=\pi^N_{hom}(\alpha,k),&\alpha\le\alpha_{hom},\\[2pt] \min\big\{k\big(\tfrac12K(\alpha b_H)+\tfrac12K(\alpha b_L)-K(\tfrac{b_H}{2})\big),1\big\}=\pi^R_{hom}(\alpha,k),&\alpha>\alpha_{hom},\end{cases}$$
--   and in the heterogeneous organization if and only if
--   $$\pi=\pi_{het}(\alpha,k)=\begin{cases}\min\big\{k\big(\tfrac12K(\alpha b_L)+\tfrac12K((1-\alpha)b_L)-K(\tfrac{b_L}{2})\big),1\big\}=\pi^N_{het}(\alpha,k),&\alpha\le\alpha_{het},\\[2pt] \min\big\{k\big(\tfrac12K(\alpha b_L)+\tfrac12K(\alpha b_H)-K(\tfrac{b_L}{2})\big),1\big\}=\pi^R_{het}(\alpha,k),&\alpha>\alpha_{het}.\end{cases}$$
--   Here $K(x)=\int_0^xF(c)\,dc$.
--
--   In particular the optimal effort exists and is unique. These closed forms are what Proposition 1 compares.
--
--   **Formalization Note** Optimality is maximization of `imPayoff` over $[0,1]$, built from DM's actual choice $d^*$ and the integral form of $K(b,d,\sigma)$. The bracket is the paper's "marginal benefit" (`mbNhom`, `mbRhom`, `mbNhet`, `mbRhet`). Assumption 2 is what makes the reactive homogeneous bracket nonnegative (Lemma 2), without which $\min\{k\cdot(\cdot),1\}$ could be negative.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), pp. 18–20, §3.3 (π^N_hom, π^R_hom p. 18; π_hom, π_het p. 19; π^N_het, π^R_het p. 20)

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem optimal_effort (P : Params) (hP : P.Standing) (hA1 : P.Assumption1)
    (hA2 : P.Assumption2) (αhom αhet : ℝ) (hhom : P.IsAlphaHom αhom)
    (hhet : P.IsAlphaHet αhet) (α k π : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1) (hk : 0 < k) :
    (IsOptimalEffort P .hom α k π ↔
      π = min (k * (if α ≤ αhom then mbNhom P α else mbRhom P α)) 1) ∧
    (IsOptimalEffort P .het α k π ↔
      π = min (k * (if α ≤ αhet then mbNhet P α else mbRhet P α)) 1) := by sorry

end OrgDiversity.Optimal
