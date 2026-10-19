-- Prove2me | Theorems.Thm_SeqSubmod_Discrete_theorem_3
-- name    : SeqSubmod.Discrete.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:56.574886+00:00
-- url     : https://prove2.me/theorems/c668e6ee-5942-4509-a84b-d1b49026ef63
-- title:
--   Theorem 3, p. 17 — an α-greedy sequence H of a sequence-non-decreasing, sequence-submodular u has u(H) ≥ (1 − e^{−α}) u(O) for every |O| ≤ |H|
-- statement:
--   Let $\mathcal S$ be a finite nonempty set of actions and $u:\mathbb H^D(\mathcal S)\to\mathbb R$ a discrete sequence function satisfying Assumption 2: $u(\emptyset)=0$, $u(A)\le u(B)$ whenever $A\prec B$ ($A$ is obtained from $B$ by deleting elements, keeping the order), and $u(C\mid A)\ge u(C\mid B)$ whenever $A\prec B$, where $u(B\mid A)=u(A\perp B)-u(A)$.
--
--   Let $\alpha\in[0,1]$ and let $H=(s_1,\dots,s_T)$ be a sequence such that for all $i\in\{1,\dots,T\}$
--   $$u\big(s_i\mid H_{[1,i-1]}\big)\ \ge\ \alpha\max_{s\in\mathcal S}u\big(s\mid H_{[1,i-1]}\big).\qquad(13)$$
--   Then for every sequence $O$ with $|O|\le T$,
--   $$u(H)\ \ge\ \Big(1-\frac{1}{e^{\alpha}}\Big)\,u(O).$$
--   In particular this holds for the optimal solution $O$ of the length-constrained problem $\max\{u(H): |H|\le T\}$, (12), which is the paper's (14), $u(H)/u(O)\ge 1-1/e^{\alpha}$.
--
--   This is the main result of §5: a sequential rule that picks, at every step, an action whose marginal value is within a factor $\alpha$ of the best one achieves a $1-e^{-\alpha}$ approximation for maximizing a non-decreasing sequence-submodular function under a length constraint. With $\alpha=1$ it is the $1-1/e$ guarantee of the plain greedy algorithm (Corollary 2), the sequence analogue of the Nemhauser–Wolsey–Fisher bound for sets.
--
--   **Formalization Note** The ratio (14) is stated in multiplied form: with $u(O)>0$ the two agree, and with $u(O)=0$ the ratio is $0/0$ while the multiplied form reads $0\le u(H)$, which Assumption 2 gives. "O denotes the optimal solution of (12)" is encoded as "for every $O$ with $|O|\le|H|$" (with $T=|H|$); this is equivalent, because the optimum exists (footnote 6) and dominates every feasible $O$. Domination $\prec$ is the subsequence order `List.Sublist`. `[Nonempty S]` is added for the maximum in (13); for empty $\mathcal S$ the claim is $0\le0$. Lean's `H[i]` and `H.take i` (0-based) stand for $s_{i+1}$ and $H_{[1,i]}$.
-- source:
--   Alaei, Makhdoumi & Malekian, Maximizing sequence-submodular functions and its application to online advertising, arXiv:1009.4153v4, p. 17, Theorem 3, (13)–(14)

import Mathlib
import Definitions.Def_SeqSubmod_Discrete_Setting

namespace SeqSubmod.Discrete
theorem theorem_3 {S : Type*} [Fintype S] [Nonempty S] (u : List S → ℝ) (hu : Assumption2 u)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (H : List S) (hH : IsAlphaGreedy u α H)
    (O : List S) (hO : O.length ≤ H.length) :
    (1 - Real.exp (-α)) * u O ≤ u H := by sorry
end SeqSubmod.Discrete
