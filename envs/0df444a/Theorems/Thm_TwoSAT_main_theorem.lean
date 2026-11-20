-- Prove2me | Theorems.Thm_TwoSAT_main_theorem
-- name    : TwoSAT.main_theorem
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-20T01:50:15.334552+00:00
-- url     : https://prove2.me/theorems/4aae5482-8596-4c18-a265-9ffe2e290517
-- title:
--   Theorem 1.1 — A one-sided sublinear-query tester for bounded-degree 2SAT
-- statement:
--   For each degree bound $d\ge1$, distance parameter $\varepsilon>0$, and slack $0<\nu<1/2$, there is a randomized tester for bounded-degree 2SAT. It accepts every satisfiable formula with probability one and rejects with probability at least $2/3$ when every assignment violates at least $\varepsilon d n$ clauses. Its worst-case query bound is $\widetilde O_{d,\varepsilon,\nu}(n^{1/2+\nu})$.
-- source:
--   Yuichi Yoshida, A One-Sided Sublinear-Query Tester for Bounded-Degree 2SAT, https://arxiv.org/abs/2611.16176, p. 2, Theorem 1.1

import Definitions.Def_YoshidaTwoSAT_QueryModel

namespace TwoSAT

theorem main_theorem :
  ∀ (d : ℕ), 1 ≤ d → ∀ ε ν : ℝ, 0 < ε → 0 < ν → ν < 1 / 2 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (q : ℕ) (alg : PMF (Tree n d q)),
        (q : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ν) * (1 + Real.log n) ^ k ∧
        ∀ F : Input n d,
          (Satisfiable F.formula → rejection alg F = 0) ∧
          (ε * d * n ≤ distance F.formula → (2 / 3 : ENNReal) ≤ rejection alg F) := by sorry

end TwoSAT
