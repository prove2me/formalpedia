-- Prove2me | Theorems.Thm_SupplyChainTheory_gs_all_or_nothing
-- name    : SupplyChainTheory.gs_all_or_nothing
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:22:29.904895+00:00
-- url     : https://prove2.me/theorems/ee066b4f-12aa-479a-960a-8f37b4e7d715
-- title:
--   Theorem 6.5: in a guaranteed-service serial system with $s_1 = 0$, every stage quotes $S^*_i = 0$ or $S^*_i = S^*_{i+1} + T_i$
-- statement:
--   **Theorem 6.5.** In the guaranteed-service serial system of Sect. 6.3.4, with holding costs
--   $h_i > 0$, $k = z_\alpha\sigma > 0$, processing times $T_i \ge 0$ and external inbound time
--   $SI_N \ge 0$, suppose $s_1 = 0$ (immediate service is required to the customer). If $S^*$
--   with $S^*_1 = 0$ minimizes the holding cost $g(S) = \sum_i h_i k\sqrt{SI_i + T_i - S_i}$ over
--   all feasible committed service times with $S_1 = 0$, then for all $i = 2, \dots, N$,
--
--   $$ S^*_i = 0 \qquad\text{or}\qquad S^*_i = S^*_{i+1} + T_i, $$
--
--   with $S^*_{N+1} = SI_N$. Each stage follows an all-or-nothing policy: it either holds no
--   safety stock and quotes the longest possible service time, or holds the most safety stock and
--   quotes zero. The book omits the proof (Problem 6.6); the cost is concave in every $S_i$ and
--   strictly concave along every direction that changes some net lead time, so a minimizer is a
--   vertex of the feasible polytope, and with $s_1 = 0$ every vertex has this form. The book notes
--   the property fails for tree systems (Figure 6.11).
--
--   **Formalization Note** The service times are real rather than integer. Since the vertices of
--   the feasible region are integral when the $T_i$ and $SI_N$ are, every integer-optimal vector
--   is also optimal over the reals, so the real statement contains the book's integer one.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 208, Sect. 6.3.4, Theorem 6.5: 'Proof. Omitted; see Problem 6.6'; the model is Eq. (6.37)-(6.42), pp. 207-208

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

theorem gs_all_or_nothing (N : ℕ) (h : ℕ → ℝ) (k : ℝ) (T : ℕ → ℝ) (SIN : ℝ)
    (hk : 0 < k) (hh : ∀ i ∈ Finset.Icc 1 N, 0 < h i) (hT : ∀ i, 0 ≤ T i) (hSI : 0 ≤ SIN)
    (S : ℕ → ℝ) (hS1 : S 1 = 0) (hfeas : GSFeasible N T SIN S)
    (hopt : ∀ S' : ℕ → ℝ, S' 1 = 0 → GSFeasible N T SIN S' →
      gsCost N h k T SIN S ≤ gsCost N h k T SIN S') :
    ∀ i ∈ Finset.Icc 2 N, S i = 0 ∨ S i = gsInbound N SIN S i + T i := by sorry

end SupplyChainTheory
