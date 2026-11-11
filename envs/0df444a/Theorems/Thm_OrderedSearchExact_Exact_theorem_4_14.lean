-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_theorem_4_14
-- name    : OrderedSearchExact.Exact.theorem_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:06.705295+00:00
-- url     : https://prove2.me/theorems/1890d2b1-d0bf-46f3-b41a-e3239adf0946
-- title:
--   Theorem 4.14 — exact ordered search at the adversary constant
-- statement:
--   There exists a single choice of the sequences $W_m,d_m,\rho_m,M_m,N_m$ satisfying the near-$\pi$ compact certificate and the parameter requirements (47)–(48). For each sufficiently large integer $n$, fix the quartic density selected by the largest $m$ with $N_m\le n$, and set $k(n)$ to the integer budget (43) with $D=2$. The greedy family (19) through step $k(n)-2$, followed by the concrete two-query exactifier, is a nonnegative normalized Laurent path from $F_n$ exactly to $1$, satisfying (1) and (2). Its greedy prefix meets the strict coefficient-mass criterion. Moreover,
--
--   $$k(n)=\frac{\ln n}{\pi}+o(\log n),$$
--
--   and an actual exact $k(n)$-query quantum algorithm for $n$-element ordered search exists. The little-o statement uses absolute discrepancy and one common family, rather than a separately selected algorithm for each fixed error tolerance. All parameter existence and construction correctness are conclusions; no progress certificate is assumed as a hypothesis.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - encoding: the greedy construction terminates within (43) and has k=ln(n)/pi+o(log n) → choose (43) as one integer budget, take its budget-2 greedy prefix and then the two-query exactifier; reason: the prescribed padding convention retains the construction and gives the displayed equality without assuming an external lower bound; an already completed path continues with zero increments
--   - encoding: m starts at 1, thresholds increase sufficiently rapidly, and the goal applies to sufficiently large n → parameter sequences are indexed by naturals with a harmless unused zero index, strictly increasing natural thresholds starting at least at 2, and finite search for the largest eligible m; reason: strict threshold growth bounds m by n; the finitely many small n use the unused index and do not affect the asymptotic or eventual correctness
--   - reading: §4.6 "Choose sequences W_m, d_m, rho_m from Proposition 4.9 … choose M_m … choose thresholds N_m" → there exist admissible parameters P for which every conclusion holds; reason: the source makes one choice and proves the theorem for it; the Lean existential asks for such a choice together with the construction's correctness, the asymptotic and the algorithm, and the admissibility predicate encodes (38), (47), (48) and D N_m ≥ M_m with D = 2
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Theorem 4.14; §4.6, (43), (47)–(49), p.23–24 (PDF p.23–24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Parameters
import Definitions.Def_OrderedSearchExact_Exact_Task

namespace OrderedSearchExact.Exact

theorem theorem_4_14 :
    ∃ P : Parameters, Admissible P ∧ AdversaryAsymptotic (familyBudget P) ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        FeasiblePrefix n (familyBudget P n - 2) (greedyPath n (familyDensity P n)) ∧
        mass (greedyPath n (familyDensity P n) (familyBudget P n - 2)) < 1 ∧
        FeasiblePath n (familyBudget P n) (constructedPath P n) ∧
        ExactAlgorithm n (familyBudget P n) := by sorry

end OrderedSearchExact.Exact
