-- Prove2me | Theorems.Thm_TestingEstimation_Dense_testing_implies_estimation
-- name    : TestingEstimation.Dense.testing_implies_estimation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:42.255205+00:00
-- url     : https://prove2.me/theorems/93dbda72-8436-48b5-a205-69129db1e1f3
-- title:
--   Theorem 2 — testing implies distance estimation with polynomial loss
-- statement:
--   There are an absolute coefficient $C>0$ and a natural exponent $d$ such that the following holds for every graph property $P$ and every real-valued testing bound $q$. Suppose that, for every real $0<\eta<1$, there is a randomized adaptive $\eta$-tester for $P$ with at most $q(\eta)$ edge queries on every execution, uniformly over all graph orders. Then for every real $0<\varepsilon<1$ there is an estimator using at most
--
--   $$C\left(\max\{1,q(\varepsilon/100)\}+\frac1\varepsilon\right)^d$$
--
--   edge queries on every execution and every input order, with
--
--   $$\Pr\left[|\widehat d-\operatorname{dist}(G,P)|\le\varepsilon\right]\ge\frac23$$
--
--   for every ordinary graph $G$. The coefficient and exponent are chosen before $P$, $q$, $\varepsilon$ and the order. The estimator is selected before the unknown graph and accesses it through its query tree alone. The property may be empty at some or all orders; no naturality, heredity, monotonicity, one-sidedness, or monotonicity of $q$ is imposed. This is the full conversion theorem about actual distance estimation, with the proof's explicit witness $c=1/100$.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: an existential c>0 and poly(max{1,q(c epsilon)},1/epsilon) → c=1/100 and C(max{1,q(epsilon/100)}+1/epsilon)^d with C and d absolute existentials; reason: page 17 explicitly proves this witness and a single monomial envelope expresses the universal bivariate polynomial bound
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Theorem 2, p. 3 (PDF 3); explicit c=1/100 in proof, p. 17 (PDF 17)

import Definitions.Def_TestingEstimation_Dense_GraphModel

noncomputable section

namespace TestingEstimation.Dense

theorem testing_implies_estimation :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ (P : Property) (q : ℝ → ℝ),
      (∀ η : ℝ, 0 < η → η < 1 →
        ∃ A : (n : ℕ) → Procedure n Bool, IsTester P η A ∧ HasQueryBound A (q η)) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ A : (n : ℕ) → Procedure n ℝ, IsEstimator P ε A ∧
          HasQueryBound A (C * (max 1 (q (ε/100)) + 1/ε)^d) := by sorry

end TestingEstimation.Dense
