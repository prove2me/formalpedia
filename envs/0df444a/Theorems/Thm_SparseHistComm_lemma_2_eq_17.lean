-- Prove2me | Theorems.Thm_SparseHistComm_lemma_2_eq_17
-- name    : SparseHistComm.lemma_2_eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:41:56.22213+00:00
-- url     : https://prove2.me/theorems/8ad46ccf-27c1-414f-9aae-29aa9e98f57b
-- title:
--   Lemma 2, (17) — accuracy requires local support identification: $P(\sum_i J_i < nk - \lfloor nD\rfloor) \le \delta + \frac{n^2\tau(k+D)}{\lfloor nD\rfloor + 1 - nD}$
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$, $0 \le D < k$, $0 \le \delta < 1$ and $0 < \tau < 1$. Let the inputs $X_1,\dots,X_n$ be independent and uniform over binary vectors with exactly $k$ active coordinates, and define the posterior lists and true-support counts
--   $$
--   I_i = \{a : P(X_i(a) = 1 \mid M_i, R) > \tau\}, \qquad J_i = |\mathrm{supp}(X_i) \cap I_i| . \tag{16}
--   $$
--   For any $(D,\delta)$-accurate protocol in either encoder model:
--
--   1. the counts $J_1,\dots,J_n$ are independent conditional on $R$;
--   2. $$
--   P\Big(\sum_{i=1}^n J_i < nk - \lfloor nD\rfloor\Big) \ \le\ \delta + \frac{n^2 \tau (k + D)}{\lfloor nD\rfloor + 1 - nD}. \tag{17}
--   $$
--
--   Accuracy forces the posterior lists to contain enough true active coordinates. The second part of Lemma 2, (18), is stated separately.
--
--   Differences from the source:
--   - encoding: protocols with any public randomness R, channels into {0,1}*, estimate from the messages and R → Protocol n d (Ω : Type, PMF (List Bool) channels and decoder measurable in r, decoder deterministic given (r, m)); reason: every probability of the paper presupposes measurability; private server randomness can be moved into R
--   - encoding: P under the prior of (16), with posteriors P(Xᵢ(a) = 1 | Mᵢ, R) → condProb / anProb with Bayes' rule and 0/0 = 0; reason: same quantities; 0/0 = 0 only concerns messages of conditional probability zero, whose lists p.15 allows to be empty
--   - encoding: J₁, …, Jₙ independent conditional on R → for every r, the joint conditional law of (J₁, …, Jₙ) given R = r is the product of its marginals; reason: definition of conditional independence for discrete variables
--   - encoding: real inequality → ENNReal.ofReal (real side) ≥ the probability in ℝ≥0∞; reason: equivalent
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Lemma 2, Eq. (16)–(17), p.8 (proof in Appendix B-A, pp.14–15)

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_IsAccurate
import Definitions.Def_SparseHistComm_threshold
import Definitions.Def_SparseHistComm_count
import Definitions.Def_SparseHistComm_condProb
import Definitions.Def_SparseHistComm_anProb
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- **Lemma 2, (17)** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8; proof in Appendix B-A, pp.14–15). For any
`(D, δ)`-accurate protocol in either encoder model and `0 < τ < 1`, the counts `Jᵢ` of (16) are
independent conditional on `R`, and
`P(∑ᵢ Jᵢ < nk − ⌊nD⌋) ≤ δ + n²τ(k + D)/(⌊nD⌋ + 1 − nD)`.

**Formalization Note** Probabilities are under the prior of Section IV (`condProb` given `R = r`,
`anProb` overall). Conditional independence is stated as the factorization of the joint
conditional law of `(J₁, …, Jₙ)` given `R = r` into its marginals. The second part of Lemma 2,
(18), is `lemma_2_eq_18`. -/
theorem lemma_2_eq_17 (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (D δ : ℝ) (hD0 : 0 ≤ D) (hDk : D < k) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (P : Protocol n d) (hP : IsAccurate P k D δ) :
    (∀ (r : P.Ω) (j : Fin n → ℕ),
      condProb P k r (fun X m => ∀ i, count P k τ i r X m = j i) =
        ∏ i, condProb P k r (fun X m => count P k τ i r X m = j i)) ∧
    anProb P k (fun r X m => ∑ i, (count P k τ i r X m : ℤ) < threshold n k D) ≤
      ENNReal.ofReal (δ + (n : ℝ) ^ 2 * τ * (k + D) / ((⌊(n : ℝ) * D⌋ : ℝ) + 1 - n * D)) := by sorry

end SparseHistComm
