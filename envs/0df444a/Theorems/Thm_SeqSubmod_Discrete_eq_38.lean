-- Prove2me | Theorems.Thm_SeqSubmod_Discrete_eq_38
-- name    : SeqSubmod.Discrete.eq_38
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:11.456039+00:00
-- url     : https://prove2.me/theorems/2f2cc078-94d0-453d-8dea-9f91629f48b3
-- title:
--   Eq. (38), proof of Theorem 3, p. 26 — each α-greedy step gains at least (α/k)(u(O) − u(H_{[1,i−1]}))
-- statement:
--   Let $\mathcal S$ be a finite nonempty set of actions and $u:\mathbb H^D(\mathcal S)\to\mathbb R$ a discrete sequence function satisfying Assumption 2 (sequence-non-decreasing with $u(\emptyset)=0$, and sequence-submodular). Let $\alpha\in[0,1]$ and let $H=(s_1,\dots,s_k)$ satisfy, for every $i\in\{1,\dots,k\}$,
--   $$u\big(s_i\mid H_{[1,i-1]}\big)\ \ge\ \alpha\max_{s\in\mathcal S}u\big(s\mid H_{[1,i-1]}\big).\qquad(13)$$
--   Then for every sequence $O$ with $|O|\le k$ and every $i\in\{1,\dots,k\}$,
--   $$u\big(s_i\mid H_{[1,i-1]}\big)\ \ge\ \frac{\alpha}{k}\Big(u(O)-u\big(H_{[1,i-1]}\big)\Big).$$
--
--   This is display (38) in the proof of Theorem 3: each greedy step closes at least an $\alpha/k$ fraction of the current gap to any feasible sequence, in particular to the optimum of problem (12). Iterating it gives (41).
--
--   **Formalization Note** The paper's $O$ is the optimal solution of (12) with $T=k$; here $O$ is any sequence of length at most $k=|H|$, which includes the optimum. The marginal value is the one defined on p. 17, $u(O\mid H_{[1,i-1]})=u(H_{[1,i-1]}\perp O)-u(H_{[1,i-1]})$; the intermediate display (37) prints $u(O\perp H_{[1,i-1]})$ instead, a slip that does not affect (38). Indices are 0-based in Lean: the statement at Lean index $i<k$ reads `H[i]` for $s_{i+1}$ and `H.take i` for $H_{[1,i]}$. The hypothesis $\alpha\le1$ is not needed for (38) but is kept so that the hypotheses are those of Theorem 3. `[Nonempty S]` is needed for the maximum in (13).
-- source:
--   Alaei, Makhdoumi & Malekian, Maximizing sequence-submodular functions and its application to online advertising, arXiv:1009.4153v4, p. 26, proof of Theorem 3, Eq. (38)

import Mathlib
import Definitions.Def_SeqSubmod_Discrete_Setting

namespace SeqSubmod.Discrete
theorem eq_38 {S : Type*} [Fintype S] [Nonempty S] (u : List S → ℝ) (hu : Assumption2 u)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (H : List S) (hH : IsAlphaGreedy u α H)
    (O : List S) (hO : O.length ≤ H.length) (i : ℕ) (hi : i < H.length) :
    α / H.length * (u O - u (H.take i)) ≤ marginal u [H[i]] (H.take i) := by sorry
end SeqSubmod.Discrete
