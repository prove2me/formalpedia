-- Prove2me | Theorems.Thm_SparseHistComm_eq_34_feasibility
-- name    : SparseHistComm.eq_34_feasibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:42:02.317666+00:00
-- url     : https://prove2.me/theorems/17f97717-1c68-4536-9280-11006d2da2c3
-- title:
--   Proof of Theorem 3 — (34) and feasibility in (12): $E\sum_i J_i \ge \Lambda_{n,k,D}(\delta + \frac{n^2(k+D)}{(\lfloor nD\rfloor + 1 - nD)\log d})$
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 3$, $0 \le D < k$, $0 \le \delta < 1$, and take $\tau = 1/\log d$ in (16) (so $0 < \tau < 1$). For every homogeneous $(D,\delta)$-accurate protocol, under the prior of Section IV:
--
--   1. the counts $J_1,\dots,J_n$ are conditionally i.i.d. given $R$: independent given $R = r$, with the same conditional law for every user, supported on $\{0,\dots,k\}$;
--   2. $$
--   P\Big(\sum_i J_i < nk - \lfloor nD\rfloor\Big) \le \delta + \frac{n^2(k + D)}{(\lfloor nD\rfloor + 1 - nD)\log d}; \tag{34}
--   $$
--   3. their common conditional law, with the existing public seed, is feasible in (12), so
--   $$
--   E\sum_i J_i \ \ge\ \Lambda_{n,k,D}\Big(\delta + \frac{n^2(k + D)}{(\lfloor nD\rfloor + 1 - nD)\log d}\Big).
--   $$
--
--   Under homogeneity the counts behave like the levels of a homogeneous randomized covering scheme, which is where $\Lambda$ enters the lower bound.
--
--   Differences from the source:
--   - generalization: for all sufficiently large d → every d ≥ 3 with k ≤ d; reason: τ = 1/log d ∈ (0, 1) once d ≥ 3, so Lemma 2 applies; when the relaxed failure probability is ≥ 1, Λ of it is 0 and (iii) is trivial; the large-d case is an instance
--   - encoding: protocols with any public randomness R, channels into {0,1}*, estimate from the messages and R → Protocol n d: Ω : Type with any probability measure, PMF (List Bool) channels and a decoder measurable in r, the decoder deterministic given (r, m); reason: every probability and expectation of the paper presupposes measurability in r; private server randomness can be moved into R; same protocols
--   - encoding: P and E under the prior of (16), with posteriors P(Xᵢ(a) = 1 | Mᵢ, R) → condProb / anProb / anExp: explicit sums over k-subsets and message strings, integrated over R; posterior by Bayes' rule with 0/0 = 0; reason: same quantities; 0/0 = 0 only concerns messages of conditional probability zero, whose lists p.15 allows to be empty
--   - encoding: Λ_{n,k,D} as a min over (L(R), p_R) → Lambda: sInf over probability laws ν of p_R on stdSimplex ℝ (Fin (k+1)); reason: objective and constraint depend only on the law of p_R; the paper's Lemma 3 shows the minimum is attained, so the value agrees
--   - encoding: real inequality between nonnegative quantities → ENNReal.ofReal (real side) ≤ value in ℝ≥0∞; reason: the ℝ≥0∞ side is the paper's (possibly infinite) quantity; equivalent
--   - encoding: conditionally i.i.d. counts → for every r: factorization of the joint conditional law, equal marginals for all users, and P(Jᵢ ≤ k | R = r) = 1; reason: definition of conditional i.i.d. for variables with values in {0, …, k}
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-C (proof of Theorem 3), Eq. (34), p.18

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_IsHomogeneous
import Definitions.Def_SparseHistComm_IsAccurate
import Definitions.Def_SparseHistComm_threshold
import Definitions.Def_SparseHistComm_Lambda
import Definitions.Def_SparseHistComm_count
import Definitions.Def_SparseHistComm_condProb
import Definitions.Def_SparseHistComm_anExp
import Definitions.Def_SparseHistComm_anProb
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- **Proof of Theorem 3, (34) and feasibility in (12)** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-C, p.18). For a
homogeneous `(D, δ)`-accurate protocol and `τ = 1/log d` (`d ≥ 3`, so `0 < τ < 1`), the counts
`J₁, …, Jₙ` are conditionally i.i.d. given `R` (independent, with identical conditional laws
supported on `{0, …, k}`), they satisfy
`P(∑ᵢ Jᵢ < nk − ⌊nD⌋) ≤ δ + n²(k + D)/((⌊nD⌋ + 1 − nD) log d)` (34), and since their common
conditional law together with the public seed is feasible in (12),
`E ∑ᵢ Jᵢ ≥ Λ_{n,k,D}(δ + n²(k + D)/((⌊nD⌋ + 1 − nD) log d))`.

**Formalization Note** Analysis probabilities and expectations as in `lemma_2_eq_17`; `log` is
`Real.logb 2`. -/
theorem eq_34_feasibility (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 3 ≤ d)
    (D δ : ℝ) (hD0 : 0 ≤ D) (hDk : D < k) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (P : Protocol n d) (hhom : IsHomogeneous P) (hP : IsAccurate P k D δ) :
    (∀ (r : P.Ω) (j : Fin n → ℕ),
      condProb P k r (fun X m => ∀ i, count P k (1 / Real.logb 2 d) i r X m = j i) =
        ∏ i, condProb P k r (fun X m => count P k (1 / Real.logb 2 d) i r X m = j i)) ∧
    (∀ (r : P.Ω) (i i' : Fin n) (j : ℕ),
      condProb P k r (fun X m => count P k (1 / Real.logb 2 d) i r X m = j) =
        condProb P k r (fun X m => count P k (1 / Real.logb 2 d) i' r X m = j)) ∧
    (∀ (r : P.Ω) (i : Fin n),
      condProb P k r (fun X m => count P k (1 / Real.logb 2 d) i r X m ≤ k) = 1) ∧
    anProb P k (fun r X m => ∑ i, (count P k (1 / Real.logb 2 d) i r X m : ℤ) < threshold n k D) ≤
      ENNReal.ofReal (δ + (n : ℝ) ^ 2 * (k + D) /
        (((⌊(n : ℝ) * D⌋ : ℝ) + 1 - n * D) * Real.logb 2 d)) ∧
    ENNReal.ofReal (Lambda n k D (δ + (n : ℝ) ^ 2 * (k + D) /
        (((⌊(n : ℝ) * D⌋ : ℝ) + 1 - n * D) * Real.logb 2 d))) ≤
      anExp P k (fun r X m => ∑ i, (count P k (1 / Real.logb 2 d) i r X m : ℝ≥0∞)) := by sorry

end SparseHistComm
