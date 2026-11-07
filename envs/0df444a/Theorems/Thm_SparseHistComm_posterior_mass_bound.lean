-- Prove2me | Theorems.Thm_SparseHistComm_posterior_mass_bound
-- name    : SparseHistComm.posterior_mass_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:41:10.265868+00:00
-- url     : https://prove2.me/theorems/d7f7e358-d333-43e0-8083-dde1a3112b3b
-- title:
--   Proof of Lemma 2 — posterior-mass bound $E[\sum_i\sum_a \hat u(a)\mathbf 1\{X_i(a)=1, a\notin I_i\}] \le n\tau(k+D)$
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$, $0 \le D < k$ and $0 < \tau < 1$. Consider any protocol (either encoder model) whose decoder satisfies $\hat u \ge 0$ and $\|\hat u\|_1 \le k + D$ on every outcome. Draw $X_1,\dots,X_n$ independently and uniformly among the $k$-subsets of $\{1,\dots,d\}$, let $I_i = \{a : P(X_i(a) = 1 \mid M_i, R) > \tau\}$ be the posterior lists of (16). Then
--   $$
--   E\Big[\sum_{i=1}^n \sum_{a=1}^d \hat u(a)\, \mathbf 1\{X_i(a) = 1,\ a \notin I_i\}\Big] \ \le\ n\tau(k + D).
--   $$
--   Each coordinate outside $I_i$ has local posterior probability at most $\tau$, and under the product prior the posterior given all messages equals the local one. Combined with the event inclusion and Markov's inequality this gives (17).
--
--   Differences from the source:
--   - generalization: the (D, δ)-accurate protocol of Lemma 2 after decoder normalization → every protocol whose decoder outputs satisfy û ≥ 0 and ‖û‖₁ ≤ k + D; reason: the display uses only these output bounds and the posterior threshold, not accuracy; the normalized accurate protocol is an instance
--   - encoding: protocols with any public randomness R, channels into {0,1}*, estimate from the messages and R → Protocol n d: Ω : Type with any probability measure, PMF (List Bool) channels and a decoder measurable in r, the decoder deterministic given (r, m); reason: every probability and expectation of the paper presupposes measurability in r; private server randomness can be moved into R; same protocols
--   - encoding: P and E under the prior of (16), with posteriors P(Xᵢ(a) = 1 | Mᵢ, R) → condProb / anProb / anExp: explicit sums over k-subsets and message strings, integrated over R; posterior by Bayes' rule with 0/0 = 0; reason: same quantities; 0/0 = 0 only concerns messages of conditional probability zero, whose lists p.15 allows to be empty
--   - encoding: real inequality between nonnegative quantities → ENNReal.ofReal (real side) ≤ value in ℝ≥0∞; reason: the ℝ≥0∞ side is the paper's (possibly infinite) quantity; equivalent
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A (proof of Lemma 2), p.15

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_postList
import Definitions.Def_SparseHistComm_anExp
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- **Proof of Lemma 2, posterior-mass bound** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A, p.15). If the decoder output
satisfies `û ≥ 0` and `‖û‖₁ ≤ k + D` on every outcome, then under the prior of Section IV, with the
posterior lists `Iᵢ` of (16),
`E[∑ᵢ ∑ₐ û(a) 1{Xᵢ(a) = 1, a ∉ Iᵢ}] ≤ nτ(k + D)`.

**Formalization Note** `E` is the analysis expectation `anExp` (prior on exactly-`k` supports,
public randomness, the protocol's channels); the integrand is a nonnegative real embedded in
`ℝ≥0∞`. The protocol is arbitrary (either encoder model). -/
theorem posterior_mass_bound (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (D : ℝ) (hD0 : 0 ≤ D) (hDk : D < k) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (P : Protocol n d) (hnonneg : ∀ r m a, 0 ≤ P.dec r m a)
    (hnorm : ∀ r m, ∑ a, |P.dec r m a| ≤ k + D) :
    anExp P k (fun r X m => ENNReal.ofReal (∑ i, ∑ a, P.dec r m a *
        (if a ∈ X i ∧ a ∉ postList P k τ i r (m i) then 1 else 0)))
      ≤ ENNReal.ofReal (n * τ * (k + D)) := by sorry

end SparseHistComm
