-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_proposition_3_2
-- name    : ProportionalTSP.Exact.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:52.552334+00:00
-- url     : https://prove2.me/theorems/6d799bf6-dcd7-4987-a9d3-07f93ec04aba
-- title:
--   Proposition 3.2 — Exact compatible-set generation and output-sensitive runtime
-- statement:
--   The prescribed process runs through every balanced feasible load and every proper Boolean coloring of its computed forest. Its output list satisfies
--   $$\operatorname{set}(\mathrm{outputs})=\mathcal C(w),\qquad |\mathrm{outputs}|=N_{m,k}=\sum_d2^{b(d)}.$$
--   Each coloring forest is acyclic and has exactly $b(d)=p(d)+|\{l>p(d):d_l=2\}|$ connected components. A uniform deterministic program generates this exact list in $O^*(N_{m,k})$ time. Multiplicity is preserved here; non-repetition is the next proposition.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: the unique minimum-cost assignment for generic costs → a finite argmin with least base-m assignment-rank tie rule, and a default only at infeasible loads; reason: the uniqueness clause is proved in Lemma 2.6; all theorem uses of canonical assignments have feasible loads
--   - encoding: deterministic polynomial or O* running time → a finite RAM program, uniform positive coefficient and natural exponent, and its evaluated instruction count; reason: the explicit language charges combinatorial instructions and allows input reals only to be copied, added, and compared; signed values are pairs of sums
--   - encoding: the process lists loads and colorings in an unspecified order → loads in increasing base-(k+1) rank and colorings in increasing binary rank, and the program must emit exactly that list; reason: any fixed order is an instance of the source process; balanced loads and proper forest colorings can both be listed in rank order with polynomial delay, so the O*(N) bound is unaffected
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Proposition 3.2, PDF p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem proposition_3_2 :
    (∀ (m k : ℕ) [NeZero m] [NeZero k], k ≤ m →
      ∀ (w : Fin m → Fin k → ℝ), Generic w →
      (enumeration w).toFinset = compatibleFamily w ∧
      (enumeration w).length = outputCount m k ∧
      (∀ d ∈ balancedLoads m k, (coloringForest w d).IsAcyclic ∧
        Fintype.card (coloringForest w d).ConnectedComponent = componentExponent d)) ∧
    EfficientEnumeration := by sorry

end ProportionalTSP.Exact
