-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_Supplement_lemma_C_2
-- name    : SFMQueryLower.EmptyMin.Supplement.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:28:09.809973+00:00
-- url     : https://prove2.me/theorems/9cd19f79-4f7b-46e5-8b56-b06ed2c3adda
-- title:
--   Lemma C.2 — every CGJS function is submodular, takes values in $[0,2]$ and has the unique minimizer $P^\pi$ with value $0$
-- statement:
--   Let $k\ge1$, $n=2k$, let $\pi$ be a permutation of $[n]$, and let $h_k^\pi\in\mathcal F$ be the CGJS function of Definition C.1 with distinguished set $P^\pi=\{\pi(1),\pi(3),\dots,\pi(2k-1)\}$. Then:
--   1. $h_k^\pi$ is submodular: $h_k^\pi(S\cup T)+h_k^\pi(S\cap T)\le h_k^\pi(S)+h_k^\pi(T)$ for all $S,T\subseteq[n]$;
--   2. $0\le h_k^\pi(S)\le2$ for every $S\subseteq[n]$;
--   3. $h_k^\pi(P^\pi)=0$;
--   4. $P^\pi$ is the unique minimizer:
--   $$h_k^\pi(P^\pi)<h_k^\pi(S)\qquad\text{for every }S\ne P^\pi.$$
--
--   The unique minimizer is what the upper bound of Theorem C.6 returns and what the lower bound of Theorem C.9 decodes.
--
--   Differences from the source:
--   - encoding: "has the unique minimizer $P^\pi$" → $h(P^\pi)<h(S)$ for every $S\ne P^\pi$; reason: this is the definition of a unique minimizer.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma C.2 (citing CGJS22, Lemma 3.3), printed p. 20 / PDF p. 21

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SFMQueryLower_EmptyMin_Supplement_CGJSFamily

set_option autoImplicit false

namespace SFMQueryLower.EmptyMin.Supplement

/-- Fox, Lemma C.2 (citing CGJS22, Lemma 3.3), printed p. 20 / PDF p. 21. All four clauses:
submodularity, values in `[0, 2]`, `h_k^π(P^π) = 0`, and `P^π` is the unique minimizer
(strictly smaller than every other value). -/
theorem lemma_C_2 (k : ℕ) (hk : 0 < k) (π : Equiv.Perm (Fin (2 * k))) :
    NonmonotoneSubmod.Shared.Submodular (cgjsFunction π) ∧
    (∀ S : Finset (Fin (2 * k)), 0 ≤ cgjsFunction π S ∧ cgjsFunction π S ≤ 2) ∧
    cgjsFunction π (cgjsMinimizer π) = 0 ∧
    ∀ S : Finset (Fin (2 * k)), S ≠ cgjsMinimizer π →
      cgjsFunction π (cgjsMinimizer π) < cgjsFunction π S := by sorry

end SFMQueryLower.EmptyMin.Supplement
