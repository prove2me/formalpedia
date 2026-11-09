-- Prove2me | Theorems.Thm_TestingEstimation_Dense_canonical_tester
-- name    : TestingEstimation.Dense.canonical_tester
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:35.670743+00:00
-- url     : https://prove2.me/theorems/1bd64283-eb0c-4cd7-98ad-661b6e888313
-- title:
--   Proposition 1 — canonical rejection rule with both N1 and N2
-- statement:
--   There is an absolute coefficient $C>0$ with the following property. Let $P$ be any graph property, $0<\tau\le1/3$, and $q$ a real uniform edge-query upper bound for a $\tau$-tester. Then there is one integer $s\ge2$, independent of the input order, with
--
--   $$s\le C\max\{1,q\}\log_2(1/\tau).$$
--
--   For every order $n\ge s$, there is a rational rejection rule $f_n:\mathcal G_s\to[0,1]\cap\mathbb Q$ invariant under every permutation of the sample positions. If $\operatorname{rej}(J)=\mathbb E_v f_n(J[v])$ for a uniform ordered injective $s$-tuple, then
--
--   $$J\in P_n\ \Longrightarrow\ \operatorname{rej}(J)\le\tau,\qquad \operatorname{dist}(J,P)\ge\tau\ \Longrightarrow\ \operatorname{rej}(J)\ge2/3.$$
--
--   The rational table is precisely a randomized rejection rule after reading the sampled induced graph. Its dependence on the original order $n$ is permitted. This result converts arbitrary adaptive, two-sided testers into the common analytic input used by the remaining items.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: an absolute O coefficient and a rational conditional rejection probability → one existential positive absolute coefficient and a rational Rule table for each original order; reason: the table is itself a finite randomized decision rule after the sampled graph is read
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Proposition 1, p. 8 (PDF 8)

import Definitions.Def_TestingEstimation_Dense_GraphModel

noncomputable section

namespace TestingEstimation.Dense

theorem canonical_tester :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Property) (τ : ℝ) (q : ℝ),
      0 < τ → τ ≤ (1:ℝ)/3 →
      (∃ A : (n : ℕ) → Procedure n Bool, IsTester P τ A ∧ HasQueryBound A q) →
      ∃ s : ℕ, 2 ≤ s ∧ (s:ℝ) ≤ C * max 1 q * logTwo (1/τ) ∧
        ∀ n : ℕ, s ≤ n → ∃ f : Rule s,
          SymmetricRule f ∧ CanonicalGuarantees P τ n f := by sorry

end TestingEstimation.Dense
