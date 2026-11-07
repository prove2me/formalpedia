-- Prove2me | Theorems.Thm_SparseHistComm_eq_29
-- name    : SparseHistComm.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:42:12.782752+00:00
-- url     : https://prove2.me/theorems/ccd9d6e9-8551-43ad-a0a7-67f7554ce828
-- title:
--   Eq. (29) — $E[\sum_i |M_i|] \ge L(\sum_i E[J_i] - 2n\sum_{j=1}^k (2^L k/(\tau\lfloor d/k\rfloor))^j)$
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$, $0 < \tau < 1$ and $L > 0$. For every protocol (either encoder model), under the prior of (16),
--   $$
--   E\Big[\sum_{i=1}^n |M_i|\Big] \ \ge\ L\Big(\sum_{i=1}^n E[J_i] - 2n \sum_{j=1}^k \Big(\frac{2^L k}{\tau\lfloor d/k\rfloor}\Big)^j\Big). \tag{29}
--   $$
--   Each identified coordinate costs about $L$ bits, up to the exceptional short-message events.
--
--   Differences from the source:
--   - generalization: the (D, δ)-accurate protocol in the proof of Lemma 2 → every protocol; reason: (29) uses only Jᵢ ≤ k and the short-message bound, not accuracy; accurate protocols are an instance
--   - encoding: protocols with any public randomness R, channels into {0,1}*, estimate from the messages and R → Protocol n d: Ω : Type with any probability measure, PMF (List Bool) channels and a decoder measurable in r, the decoder deterministic given (r, m); reason: every probability and expectation of the paper presupposes measurability in r; private server randomness can be moved into R; same protocols
--   - encoding: P and E under the prior of (16), with posteriors P(Xᵢ(a) = 1 | Mᵢ, R) → condProb / anProb / anExp: explicit sums over k-subsets and message strings, integrated over R; posterior by Bayes' rule with 0/0 = 0; reason: same quantities; 0/0 = 0 only concerns messages of conditional probability zero, whose lists p.15 allows to be empty
--   - encoding: real inequality between nonnegative quantities → ENNReal.ofReal (real side) ≤ value in ℝ≥0∞; reason: the ℝ≥0∞ side is the paper's (possibly infinite) quantity; equivalent
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (29), Appendix B-A (proof of Lemma 2), p.16

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_count
import Definitions.Def_SparseHistComm_anExp
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- **Eq. (29)** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A, p.16). For every protocol (either encoder model),
`0 < τ < 1` and every positive length `L`, under the prior of Section IV,
`E[∑ᵢ |Mᵢ|] ≥ L(∑ᵢ E[Jᵢ] − 2n ∑_{j=1}^k (2^L k/(τ⌊d/k⌋))^j)`.

**Formalization Note** Expectations are `anExp` in `ℝ≥0∞`; `E[Jᵢ] ≤ k` is finite, so `toReal` is
exact, and the real right side is embedded by `ENNReal.ofReal` (the bound is trivial when it is
negative). -/
theorem eq_29 (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (L : ℝ) (hL : 0 < L) (P : Protocol n d) :
    ENNReal.ofReal (L * (∑ i, (anExp P k (fun r X m => (count P k τ i r X m : ℝ≥0∞))).toReal
        - 2 * n * ∑ j ∈ Finset.Icc 1 k, ((2 : ℝ) ^ L * k / (τ * ((d / k : ℕ) : ℝ))) ^ j))
      ≤ anExp P k (fun _ _ m => ∑ i, ((m i).length : ℝ≥0∞)) := by sorry

end SparseHistComm
