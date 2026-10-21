-- Prove2me | Theorems.Thm_SeqSubmod_Discrete_eq_41
-- name    : SeqSubmod.Discrete.eq_41
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:55.969775+00:00
-- url     : https://prove2.me/theorems/68b4e0f9-2f2b-4a81-9826-dd0b1faf07aa
-- title:
--   Eq. (41), proof of Theorem 3, p. 27 — an α-greedy H has u(H) ≥ (1 − (1 − α/k)^k) u(O) for every |O| ≤ k = |H|
-- statement:
--   Let $\mathcal S$ be a finite nonempty set of actions and $u:\mathbb H^D(\mathcal S)\to\mathbb R$ satisfy Assumption 2. Let $\alpha\in[0,1]$ and let $H=(s_1,\dots,s_k)$ satisfy the greedy condition (13) at every position $i\in\{1,\dots,k\}$. Then for every sequence $O$ with $|O|\le k$,
--   $$u(H)\ \ge\ \Big(1-\Big(1-\frac{\alpha}{k}\Big)^{k}\Big)\,u(O).$$
--
--   This is the first form of display (41) in the proof of Theorem 3, obtained by unrolling the recursion (40), $u(H_{[1,i]})\ge\frac{\alpha}{k}u(O)+(1-\frac{\alpha}{k})u(H_{[1,i-1]})$, over $i=1,\dots,k$. It is the finite-$k$ version of Theorem 3's guarantee.
--
--   **Formalization Note** The paper writes $u(H_{[1,k]})$, which is $u(H)$ since $k=|H|$. The paper's $O$ is the optimum of (12) with $T=k$; here $O$ is any sequence of length at most $k$. At $k=0$ Lean's $\alpha/0=0$ gives the factor $1-1^0=0$ and the statement reads $0\le u(\emptyset)$, which holds. The second printed form of (41), $\big(1-((1-\alpha/k)^{k/\alpha})^{\alpha}\big)u(O)$, is a rewriting that is undefined at $\alpha=0$ and is not stated.
-- source:
--   Alaei, Makhdoumi & Malekian, Maximizing sequence-submodular functions and its application to online advertising, arXiv:1009.4153v4, p. 27, proof of Theorem 3, Eq. (41)

import Mathlib
import Definitions.Def_SeqSubmod_Discrete_Setting

namespace SeqSubmod.Discrete
theorem eq_41 {S : Type*} [Fintype S] [Nonempty S] (u : List S → ℝ) (hu : Assumption2 u)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (H : List S) (hH : IsAlphaGreedy u α H)
    (O : List S) (hO : O.length ≤ H.length) :
    (1 - (1 - α / H.length) ^ H.length) * u O ≤ u H := by sorry
end SeqSubmod.Discrete
