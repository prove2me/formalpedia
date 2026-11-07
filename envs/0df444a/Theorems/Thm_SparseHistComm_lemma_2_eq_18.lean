-- Prove2me | Theorems.Thm_SparseHistComm_lemma_2_eq_18
-- name    : SparseHistComm.lemma_2_eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:42:13.570334+00:00
-- url     : https://prove2.me/theorems/13c18406-571a-4d9d-a6fb-4c0542c1b93f
-- title:
--   Lemma 2, (18) — with $\tau = 1/\log d$: $E[\sum_i |M_i|] \ge E[\sum_i J_i]\log d - O(\log\log d)$, constant depending only on $n, k$
-- statement:
--   Fix $n \ge 1$ and $k \ge 1$. There are a constant $C$ and a dimension $d_0$, depending only on $n$ and $k$, such that for every $d \ge d_0$ and every protocol on $d$ coordinates (either encoder model), with $\tau = 1/\log d$ in (16) and the prior of Section IV,
--   $$
--   E\Big[\sum_{i=1}^n |M_i|\Big] \ \ge\ E\Big[\sum_{i=1}^n J_i\Big] \log d - C \log\log d . \tag{18}
--   $$
--   Here $\log$ is base 2. Every true active coordinate identified by the posterior lists costs $\log d$ bits to first order.
--
--   Differences from the source:
--   - generalization: for any (D, δ)-accurate protocol → for every protocol; reason: the proof (29)–(30) does not use accuracy, and the accurate protocols are among all protocols, so the source's claim is the special case
--   - reading: "for all sufficiently large d, … − O(log log d)"; "the hidden constant depends only on n, k" (p.16) → ∃ C ∃ d₀ chosen from n, k, then ∀ d ≥ d₀ ∀ protocols; reason: the stated dependence of the constant, uniform over protocols as Theorem 3's proof needs
--   - encoding: protocols with any public randomness, channels into {0,1}* → Protocol n d (Ω : Type, measurable PMF (List Bool) channels, decoder measurable); reason: same protocols, measurability presupposed by the paper's expectations
--   - encoding: E under the prior of (16) → anExp with Bayes' rule posteriors and 0/0 = 0; reason: same quantity
--   - encoding: real inequality → ENNReal.ofReal (real side) ≤ the expectation in ℝ≥0∞; reason: equivalent
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Lemma 2, Eq. (18), p.8; proved as Eq. (30), Appendix B-A, p.16

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_count
import Definitions.Def_SparseHistComm_anExp
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- **Lemma 2, (18)** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8; proved as (30), Appendix B-A, p.16). With
`τ = 1/log d` and fixed `n, k`, for all sufficiently large `d`,
`E[∑ᵢ |Mᵢ|] ≥ E[∑ᵢ Jᵢ] log d − O(log log d)`; "the hidden constant depends only on n, k".

**Formalization Note** `−O(log log d)` is `∃ C d₀` chosen from `n, k` alone, before `d` and the
protocol, so the bound is uniform over protocols. It is stated for every protocol on `d`
coordinates: the proof (29)–(30) does not use accuracy (a declared generalization). `log` is
`Real.logb 2`. -/
theorem lemma_2_eq_18 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ P : Protocol n d,
      ENNReal.ofReal ((anExp P k (fun r X m =>
            ∑ i, (count P k (1 / Real.logb 2 d) i r X m : ℝ≥0∞))).toReal * Real.logb 2 d
          - C * Real.logb 2 (Real.logb 2 d))
        ≤ anExp P k (fun _ _ m => ∑ i, ((m i).length : ℝ≥0∞)) := by sorry

end SparseHistComm
