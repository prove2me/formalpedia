-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_theorem_23
-- name    : PolynomialSampling137.OneThird.Supplement.theorem_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:56:47.658867+00:00
-- url     : https://prove2.me/theorems/e8d4d6bc-2e72-4d35-a9d9-5abc88ed3da3
-- title:
--   Theorem 23 — Few nonlinear ancestors: every non-dyadic parameter, arbitrary depth, and exact q-dependent one-third constant
-- statement:
--   Fix $q\ge0$ and any non-dyadic real $p\in(0,1)$. There exists $c_{q,p}>0$, independent of every $s\ge0$, $N\ge1$ and $Q:\mathbb F_2^s\to\mathbb F_2^N$, such that if every coordinate of $Q$ belongs to $\mathcal C_q$, then
--   $$\operatorname{Ov}(P_Q,\operatorname{Ber}(p)^{\otimes N})\le\exp(-c_{q,p}N).$$
--   For $p=1/3$, uniformly in $q,s,N$, the explicit coefficient is $c_q=2^{-12\cdot2^q}/729$. Each coordinate has at most $q$ distinct AND/OR ancestors; there is no global nonlinear-gate bound and no restriction on XOR/NOT count, depth, finite fan-in or Boolean degree. This companion theorem extends separation to a structural circuit class.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 23, printed p. 26; PDF p. 28

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_Circuits

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem theorem_23 :
    (∀ (q : ℕ) (p : ℝ), 0 < p → p < 1 → NonDyadic p →
      ∃ c : ℝ, 0 < c ∧ ∀ (s N : ℕ), 1 ≤ N → ∀ Q : Word s → Word N,
        (∀ i, InCircuitClass q (fun x => Q x i)) →
        overlap (samplerMass Q) (bernoulliProductMass p N) ≤ Real.exp (-c * N)) ∧
    (∀ (q s N : ℕ), 1 ≤ N → ∀ Q : Word s → Word N,
      (∀ i, InCircuitClass q (fun x => Q x i)) →
      overlap (samplerMass Q) (bernoulliProductMass (1/3) N) ≤
        Real.exp (-((2 : ℝ) ^ (-12 * (2 : ℤ) ^ q) / 729) * N)) := by sorry

end PolynomialSampling137.OneThird.Supplement
