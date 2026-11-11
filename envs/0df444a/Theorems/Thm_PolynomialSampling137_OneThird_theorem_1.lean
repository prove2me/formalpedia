-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_theorem_1
-- name    : PolynomialSampling137.OneThird.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T10:26:45.889839+00:00
-- url     : https://prove2.me/theorems/e85857b5-55ba-41e9-aa8b-e3ca6f5dbaa2
-- title:
--   Theorem 1 — Khodabandeh–Shinkar acceptance gaps
-- statement:
--   For each integer $d\ge1$ there are positive numbers $\delta_{d,r}$, one for each integer $r\ge1$, independent of the seed length, such that every Boolean $q$ of degree-$d$ rank at most $r$ satisfies
--
--   $$|\Pr[q(U_s)=1]-1/3|\ge\delta_{d,r}.$$
--
--   The degree-at-most-$d$ class has the same gap $\delta_d=\delta_{d,1}$. Moreover, for each real non-dyadic $p\in(0,1)$ there exists $\delta_{d,p}>0$ such that every degree-at-most-$d$ function on every finite seed space satisfies
--
--   $$|\Pr[q(U_s)=1]-p|\ge\delta_{d,p}.$$
--
--   This is the literature acceptance-gap input restated in the paper, including its non-dyadic-real clause. It is an open proof obligation here; no companion-project literature assumption is treated as a proof.
--
--   Differences from the source:
--   - encoding: binary vector spaces and Boolean multilinear degree → Fin-indexed ZMod 2 words and evaluation of multilinear MvPolynomial representatives; reason: the same finite binary spaces and the unique Boolean polynomial, including constants and dimension zero
--   - encoding: one positive acceptance-gap witness for each positive rank, with the degree-only witness equal to the rank-one witness → a function δ on natural ranks, constrained only at positive ranks, with the degree-only clause using δ 1; reason: simultaneous choice records the source witness family and changes no instance
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 1, printed p. 8 / PDF p. 10; citing [KS26, Theorem 6.4, Remark 6.5, Theorem A.8]

import Definitions.Def_PolynomialSampling137_OneThird_BooleanSources

namespace PolynomialSampling137.OneThird

/-- Zhong, Theorem 1, including the degree-only and arbitrary non-dyadic-real clauses. -/
theorem theorem_1 (d : ℕ) (hd : 1 ≤ d) :
    ∃ δ : ℕ → ℝ,
      (∀ r : ℕ, 1 ≤ r → 0 < δ r ∧ RankGap d r (1 / 3) (δ r)) ∧
      DegreeGap d (1 / 3) (δ 1) ∧
      (∀ p : ℝ, 0 < p → p < 1 → NonDyadic p →
        ∃ ε : ℝ, 0 < ε ∧ DegreeGap d p ε) := by sorry

end PolynomialSampling137.OneThird
