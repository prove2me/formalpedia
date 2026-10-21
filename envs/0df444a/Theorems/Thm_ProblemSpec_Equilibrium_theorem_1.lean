-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_theorem_1
-- name    : ProblemSpec.Equilibrium.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:31.367136+00:00
-- url     : https://prove2.me/theorems/681e344b-7d7f-40ad-85a2-94d065ddc29c
-- title:
--   Theorem 1, p. 9 — every symmetric equilibrium is (r∗, m∗); N∗ rises where designers guess, falls elsewhere, and is free of S_g
-- statement:
--   Consider the crowdsourcing contest of §3 under the standing assumptions. Then:
--
--   1. **Uniqueness of the symmetric equilibrium.** For every $N>1$, $S_r,S_g\ge0$ with $\bar r(N)\ge0$, every symmetric pure-strategy equilibrium $(r,m)$ of the designers' game with $N$ participants satisfies
--   $$r=r^*=\begin{cases}\bar r^g,& S_r<\bar r^g,\\ S_r,&\bar r^g\le S_r\le\bar r,\\ \bar r,& S_r>\bar r,\end{cases}\qquad m=m^*=\frac{A(N-1)}{N^2c_3},\ c_3=h(S_g),$$
--   where $\bar r^g=\frac{1}{\ln(1/p)}\ln\big(\frac{N-1}{N^2}\frac{\nu w}{\mu}\frac{A}{c_2}\frac{1}{\ln(1/p)}-\frac{c_g}{c_2}\frac{1}{\ln(1/p)}\big)$ and $\bar r=\frac{1}{\ln(1/p)}\ln\big(\frac{N-1}{N^2}\frac{w}{\mu}\frac{A}{c_2}\frac{1}{\ln(1/p)}\big)$.
--   2. **$N^*$ does not depend on $S_g$.** For $S_r,S_g,S_g'\ge0$, $N$ is the free-entry level at $(S_r,S_g)$ if and only if it is the free-entry level at $(S_r,S_g')$.
--   3. **$N^*$ and disclosed objectives.** Let $S\subseteq[0,\infty)$ and let $S_r\mapsto N^*(S_r)$ assign to each $S_r\in S$ the free-entry level at $(S_r,S_g)$, with $\bar r(N^*(S_r))\ge0$. Then $N^*$ is strictly increasing on the points of $S$ where designers guess ($S_r<\bar r^g(N^*(S_r))$), and non-increasing on the points where they do not ($S_r\ge\bar r^g(N^*(S_r))$).
--   4. **Execution guidance raises trial effort.** For $N>1$, $S_r\ge0$, $0\le S_g<S_g'$ with $\bar r(N)\ge0$, if $(r,m)$ is a symmetric equilibrium at $S_g$ and $(r',m')$ one at $S_g'$, then $m<m'$ and $r=r'$.
--
--   The theorem says how a seeker's problem statement shapes participation: disclosing conceptual objectives attracts designers while it saves them guessing, and deters them once they no longer guess; execution guidance changes only the number of trials, not entry.
--
--   **Formalization Note** $N^*$ is the free-entry level of App. p. 2 (the $N$-th designer's utility equals $s$ and every later designer's is below $s$), not a closed form. The existence half of "the unique symmetric equilibrium … are as follows" is omitted because it fails for some admissible parameters; the "first increases … then decreases" ordering is stated region by region, not as a claim that the guessing region is an initial segment; "decreases" is read weakly, as in the paper's proof ($\le 0$). Added hypotheses: $0<p<1$, $s>0$, $h>0$ and strictly decreasing, and $\bar r\ge0$ (the page's "$w$ is not trivially small").
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), p. 9 (PDF 9), Theorem 1; p. 10 (PDF 10), discussion of m∗ and Sg

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- Theorem 1, p. 9 (PDF 9), with the reading of p. 10. Under the standing assumptions:
(i) given `N > 1` participants (with `Sr, Sg ≥ 0` and `r̄(N) ≥ 0`), every symmetric equilibrium
`(r, m)` is `(r∗(N), m∗(N))`: `r∗ = r̄^g` if `Sr < r̄^g`, `Sr` if `r̄^g ≤ Sr ≤ r̄`, `r̄` if
`Sr > r̄`, and `m∗ = A(N−1)/(N² h(Sg))`;
(ii) the free-entry number of participants `N∗` does not depend on `Sg`;
(iii) along any assignment `Sr ↦ N∗(Sr)` of free-entry levels (with `r̄(N∗) ≥ 0`), `N∗` strictly
increases in `Sr` where designers guess (`Sr < r̄^g(N∗)`) and does not increase where they do
not (`Sr ≥ r̄^g(N∗)`);
(iv) given `N`, more execution guidance (larger `Sg`) strictly raises the equilibrium number of
trials and leaves the number of incorporated objectives unchanged. -/
theorem theorem_1 (P : Params) (hP : P.Standing) :
    (∀ Sr Sg N r m : ℝ, 0 ≤ Sr → 0 ≤ Sg → 1 < N → 0 ≤ rbar P N →
        IsSymEq P Sr Sg N r m → r = rstar P N Sr ∧ m = mstar P Sg N) ∧
    (∀ Sr Sg Sg' N : ℝ, 0 ≤ Sr → 0 ≤ Sg → 0 ≤ Sg' →
        (IsFreeEntry P Sr Sg N ↔ IsFreeEntry P Sr Sg' N)) ∧
    (∀ (Sg : ℝ) (Nstar : ℝ → ℝ) (S : Set ℝ), 0 ≤ Sg → S ⊆ Set.Ici 0 →
        (∀ Sr ∈ S, IsFreeEntry P Sr Sg (Nstar Sr) ∧ 0 ≤ rbar P (Nstar Sr)) →
        StrictMonoOn Nstar {Sr | Sr ∈ S ∧ Guessing P (Nstar Sr) Sr} ∧
        AntitoneOn Nstar {Sr | Sr ∈ S ∧ ¬ Guessing P (Nstar Sr) Sr}) ∧
    (∀ Sr Sg Sg' N r m r' m' : ℝ, 0 ≤ Sr → 0 ≤ Sg → Sg < Sg' → 1 < N → 0 ≤ rbar P N →
        IsSymEq P Sr Sg N r m → IsSymEq P Sr Sg' N r' m' → m < m' ∧ r = r') := by sorry

end ProblemSpec.Equilibrium
