-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_lemma_7_8
-- name    : SatisfiableOrderingCSP.Optimal.lemma_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:49:13.006816+00:00
-- url     : https://prove2.me/theorems/98efc2a4-94ec-4458-b2c7-9ee4948f35fe
-- title:
--   Lemma 7.8 — influential coordinates of rank prefixes
-- statement:
--   There is an absolute C>0 such that the following holds for any number n0 of base variables with multislices of a common positive length, possibly different finite alphabets, and a common valid integral noise count. For each variable, give a conditional probability distribution of a real score, with arbitrary private randomness, and suppose the uniform mixture score distribution has continuous CDF. Suppose the sum of noisy influences is at most Imax for every [0,1]-valued function on each multislice. For every 0<lambda<=1 the set of coordinates influential by at least lambda for at least one rank prefix, at at least one real threshold and base variable, has cardinality at most C(1+n0*Imax/lambda^2). The constant precedes every alphabet, length, score law, and parameter. The assertion also includes the vacuous zero-variable case.
--
--   Differences from the source:
--   - encoding: theta-noise on each multislice and theta_N=2 floor(bN/2)/N → integer counts d per supported symbol, with counts 2*floor(bN/2) on length N and floor(bN/2) on length N/2; reason: these are exactly the printed integral noise counts; zero-count ambient symbols are omitted from the cyclic support order
--   - encoding: real scores depending on a multislice point and private randomness, with continuous distribution → a real probability-measure kernel and continuity of its finite-mixture CDF; reason: conditional kernels retain arbitrary real score distributions; continuity of the CDF is equivalent to absence of atoms
--   - encoding: O(1+n0*Imax/lambda^2) independently of the number of coordinates → one positive real constant quantified before all lengths and alphabets; reason: this is the absolute big-O conclusion, not a length-dependent bound
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Lemma 7.8, printed p. 48 (PDF p. 51); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Multislices

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem lemma_7_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ n n₀ : ℕ, ∀ q : Fin n₀ → ℕ,
      ∀ (H : (v : Fin n₀) → Histogram n (q v)) (d : ℕ),
        (∀ v, (H v).NoiseValid d) →
        ∀ (R : (v : Fin n₀) → ScoreKernel n (q v)),
          (∀ v, ContinuousScore (H v) (R v)) →
          ∀ Imax : ℝ,
            (∀ v (f : (Fin n → Fin (q v)) → ℝ),
              (∀ x ∈ (H v).strings, 0 ≤ f x ∧ f x ≤ 1) →
              (∑ i, (H v).noisyInfluence d f i) ≤ Imax) →
            ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
              ((influentialPrefixes H d R lam).card : ℝ) ≤
                C * (1 + n₀ * Imax / lam^2) := by sorry

end SatisfiableOrderingCSP.Optimal
