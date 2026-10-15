-- Prove2me | Theorems.Thm_StrictCompatLB_RegularDegree_subcritical_of_A19
-- name    : StrictCompatLB.RegularDegree.subcritical_of_A19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:58.57696+00:00
-- url     : https://prove2.me/theorems/2ce0e68d-2a25-40e5-915e-f13dbec0f4a7
-- title:
--   Appendix A, (A.19) — condition (A.19) implies the subcriticality condition (uniform weights)
-- statement:
--   Let $\{G_N\}_{N\ge1}$ be any sequence of bipartite graphs between $N$ servers and $M(N)$ dispatchers, and let $d\ge 2$. If
--   $$\limsup_{N\to\infty}\max_{v\in V_N}\frac{N}{M(N)}\sum_{w\in W_N}\frac{\mathbb 1\{(v,w)\in E_N\}}{|\mathcal N_w|}\le 1, \tag{A.19}$$
--   then $\{G_N\}$ satisfies the subcriticality condition (3.2) of Definition 3.3 with sample size $d$.
--
--   This is the reduction stated on p. 34: (3.2) only requires *some* choice of weights $\gamma^U_w$, and for the uniform choice $\gamma^U_w(v)=1/\min(d,|\mathcal N_w|)$ on $U$, the left-hand side of (3.2) equals that of (A.19). Lemma A.5 and the random-graph results of the paper verify (A.19) instead of (3.2).
--
--   **Formalization Note** The statement is deterministic. The subcriticality condition is the one in the mission's definition file: weights constrained only on nonempty $U$, normaliser $\binom{|\mathcal N_w|}{\min(d,|\mathcal N_w|)}$. Both limsup conditions are written as "for every $\varepsilon>0$, eventually every server's value is at most $1+\varepsilon$". The hypothesis $d\ge2$ is the model's standing assumption (§2); the reduction does not use it beyond $d\ge 1$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 34, Appendix A, display (A.19)

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions

open Finset Filter

namespace StrictCompatLB.RegularDegree

theorem subcritical_of_A19 (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (hG : SatisfiesA19 M G) :
    StrictCompatLB.MeanField.IsSubcritical d M G := by sorry

end StrictCompatLB.RegularDegree
