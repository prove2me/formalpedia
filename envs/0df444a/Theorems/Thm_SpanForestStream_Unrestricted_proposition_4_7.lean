-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_proposition_4_7
-- name    : SpanForestStream.Unrestricted.proposition_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:45.032558+00:00
-- url     : https://prove2.me/theorems/bdade5a8-ea0b-4477-9a08-c6895ddacb6f
-- title:
--   Proposition 4.7 — sparse product relation: I(S^k; M) = Ω(k log(k+1) log(2 + m/log(k+1)) log(U/m))
-- statement:
--   There are absolute constants $k_0,C_1,C_2,c>0$ such that for every even $k\ge k_0$ and all integers $m\ge C_1\log_2(k+1)$ and $U\ge C_2m$ there is a product hard law for $k$ universal-relation instances, built from one law $D$ of a pair $T\subsetneq S$ whose source set $S$ is uniform among the $m$-subsets of $[U]$, with the following property. Every randomized one-way protocol obeying both Markov conditions of Lemma 4.5 (message from $S^k$, any shared random seed included in the message; output from $(M,T^k)$) and solving all $k$ instances with probability at least $1/2$ obeys
--   $$I(S^k;M)\ge c\,k\log_2(k+1)\,\log_2\Big(2+\frac{m}{\log_2(k+1)}\Big)\log_2\frac Um.\qquad(4.19)$$
--
--   This is the $k$-fold information bound that the graph reduction of Proposition 4.8 charges block by block.
--
--   Differences from the source:
--   - encoding: 'for all sufficiently large even k', 'm ≥ C1 log(k + 1)', 'U ≥ C2 m', Ω(·) → ∃ absolute k0, C1, C2, c > 0 before k, m, U; reason: asymptotic thresholds and O/Ω as explicit absolute constants
--   - encoding: a product hard law for k instances with independent uniform m-subset sources → k independent copies of one pair law D with D[S] uniform on m-subsets of [U] and T ⊊ S on its support; reason: the paper's product hard law
--   - encoding: the protocol → message kernel from S^k, output kernel from (M, T^k) with fresh coins, outputs in Option [U]; reason: as in Lemma 4.5
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 31 (PDF 34), Proposition 4.7, Eq. (4.19)

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Info
import Definitions.Def_SpanForestStream_Unrestricted_Protocols

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Proposition 4.7 (sparse product relation, external information): there are absolute
`k₀, C₁, C₂, c > 0` such that for every even `k ≥ k₀`, `m ≥ C₁ log₂(k+1)` and `U ≥ C₂ m` there is a
hard law `D` of a pair `T ⊊ S` with `S` uniform among the `m`-subsets of `[U]`, such that every
`k`-fold one-way protocol on `k` independent copies solving all `k` universal-relation instances
with probability at least `1/2` has
`I(S^k; M) ≥ c k log₂(k+1) log₂(2 + m / log₂(k+1)) log₂(U/m)`. -/
theorem proposition_4_7 :
    ∃ (k₀ : ℕ) (C₁ C₂ c : ℝ), 0 < C₁ ∧ 0 < C₂ ∧ 0 < c ∧
      ∀ (k m U : ℕ), k₀ ≤ k → Even k → C₁ * Real.logb 2 (k + 1) ≤ m → C₂ * m ≤ U →
      ∃ D : PMF (Finset (Fin U) × Finset (Fin U)),
        D.map Prod.fst = uniformSubsets U m ∧ (∀ st ∈ D.support, st.2 ⊂ st.1) ∧
        ∀ {Msg : Type} (msg : (Fin k → Finset (Fin U)) → PMF Msg)
          (out : Msg → (Fin k → Finset (Fin U)) → PMF (Fin k → Option (Fin U))),
          (1 / 2 : ℝ≥0∞) ≤ probOf (oneWayJoint D msg out)
              {ω | ∀ j, URSolves (ω.1 j).1 (ω.1 j).2 (ω.2.2 j)} →
          ENNReal.ofReal (c * k * Real.logb 2 (k + 1) *
              Real.logb 2 (2 + m / Real.logb 2 (k + 1)) * Real.logb 2 (U / m)) ≤
            mutualInfo (oneWayJoint D msg out) (fun ω => fun j => (ω.1 j).1)
              (fun ω => ω.2.1) := by sorry

end SpanForestStream.Unrestricted
