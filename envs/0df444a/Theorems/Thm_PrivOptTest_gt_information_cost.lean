-- Prove2me | Theorems.Thm_PrivOptTest_gt_information_cost
-- name    : PrivOptTest.gt_information_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:17.795705+00:00
-- url     : https://prove2.me/theorems/c3be7fae-9753-4f8e-a50b-a53063193f35
-- title:
--   Proof of Theorem 3.1, p.15 — Greater-Than has internal information cost Ω(log ℓ) [BW11; Vio15]
-- statement:
--   There are $c>0$ and $\ell_0$ such that for every $\ell\ge\ell_0$ there is a distribution $\mu_\ell$ on $\{2,\dots,2^\ell+1\}^2$ such that every well-formed two-party protocol whose common output equals $\mathrm{GT}_\ell(i,j)=\mathbf 1\{i\ge j\}$ except with probability at most $1/10$ (over $(i,j)\sim\mu_\ell$ and the coins) has internal information cost
--   $$I(I;T\mid J)+I(J;T\mid I)\ge c\log_2\ell .$$
--
--   The paper cites this result of Braverman–Weinstein and Viola; with Lemma 2.2 and (7) it gives Theorem 3.1.
--
--   Differences from the source:
--   - reading: Ω(log ℓ) → ∃ c > 0, ℓ₀, ∀ ℓ ≥ ℓ₀; reason: the usual meaning of an asymptotic lower bound
--   - reading: "computing GT_ℓ with error at most 1/10" → distributional error at most 1/10 under μ_ℓ; a run that never stops counts as an error; reason: the stronger reading: worst-case error 1/10 implies it, and [BW11] is distributional
--   - reading: "every protocol" → every well-formed protocol of the model: private and public coins, arbitrary measurable message spaces, any number of rounds; reason: the protocols of Definition 1.2 to which the bound is applied
--   - encoding: index set {2, …, 2^ℓ + 1} → Fin (2^ℓ) via i ↦ i − 2; reason: order-preserving, so GT is unchanged
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.1, p.15

import Mathlib
import Definitions.Def_PrivOptTest_Protocol
import Definitions.Def_PrivOptTest_infoCost

open MeasureTheory

namespace PrivOptTest

/-- **The information cost of Greater-Than** (proof of Theorem 3.1, p.15, citing [BW11; Vio15]). There
is a distribution `μ_ℓ` on `{2, …, 2^ℓ + 1}²` such that every protocol computing
`GT_ℓ(i, j) = 1{i ≥ j}` with error at most `1/10` has internal information cost `Ω(log ℓ)`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.1, p.15.

**Formalization Note.** `Ω(log ℓ)`: there are `c > 0` and `ℓ₀` such that for every `ℓ ≥ ℓ₀` the
distribution exists. The index set `{2, …, 2^ℓ + 1}` is `Fin (2^ℓ)` by `i ↦ i − 2`, which preserves
`GT`. Error is distributional, under `μ_ℓ` and the protocol's coins; a run that never stops counts as an
error. Protocols are arbitrary well-formed two-party protocols (private and public coins, any
measurable message spaces, any number of rounds). Information cost is `infoCost` in bits. -/
theorem gt_information_cost :
    ∃ c : ℝ, 0 < c ∧ ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∃ μ : PMF (Fin (2 ^ ℓ) × Fin (2 ^ ℓ)),
      ∀ Pr : Protocol (Fin (2 ^ ℓ)) Bool, Pr.IsWellFormed →
        (∑ p : Fin (2 ^ ℓ) × Fin (2 ^ ℓ),
            μ p * Pr.outputLaw p.1 p.2 {o | o ≠ Sum.inl (decide (p.2 ≤ p.1))}) ≤ 1 / 10 →
          ENNReal.ofReal (c * Real.logb 2 ℓ) ≤ infoCost μ fun i j => Pr.transcriptLaw i j := by sorry

end PrivOptTest
