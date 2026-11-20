-- Prove2me | Theorems.Thm_TwoSAT_exact_tester
-- name    : TwoSAT.exact_tester
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-20T01:50:00.741185+00:00
-- url     : https://prove2.me/theorems/d4336cf6-8556-4bf0-943c-b625781ab3e9
-- title:
--   A one-sided tester for clauses on two distinct variables
-- statement:
--   For formulas in which every clause uses two distinct variables, a randomized incidence-query tester accepts every satisfiable input with probability one and rejects every $\varepsilon$-far input with probability at least $2/3$, using $\widetilde O_{d,\varepsilon,\nu}(n^{1/2+\nu})$ queries.
-- source:
--   Yuichi Yoshida, A One-Sided Sublinear-Query Tester for Bounded-Degree 2SAT, https://arxiv.org/abs/2611.16176, Section 6.3, exact-width tester

import Definitions.Def_YoshidaTwoSAT_QueryModel

namespace TwoSAT

theorem exact_tester :
  ∀ (d : ℕ), 1 ≤ d → ∀ ε ν : ℝ, 0 < ε → 0 < ν → ν < 1 / 2 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (q : ℕ) (alg : PMF (Tree n d q)),
        (q : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ν) * (1 + Real.log n) ^ k ∧
        ∀ F : Input n d, Reduction.Exact F →
          (Satisfiable F.formula → rejection alg F = 0) ∧
          (ε * d * n ≤ distance F.formula → (2 / 3 : ENNReal) ≤ rejection alg F) := by sorry

end TwoSAT
