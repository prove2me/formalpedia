-- Prove2me | Theorems.Thm_RGGDetect_theorem_3
-- name    : RGGDetect.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:02.475203+00:00
-- url     : https://prove2.me/theorems/09ea5c22-01f4-482b-8dde-5813f8ed3402
-- title:
--   Theorem 3 — Fourier reduction $\Delta\le2\sum_{k=2}^{K-1}\binom{n'}k\mathrm{Post}(\eta_k)+o(1/n)$
-- statement:
--   For any fixed integer $K>2/\delta$, the quantity $\Delta$ of (9) satisfies
--
--   $$
--   \Delta\le2\sum_{k=2}^{K-1}\binom{n'}{k}\mathrm{Post}(\eta_k)+o(1/n),
--   $$
--
--   with $\mathrm{Post}$ defined by (5) and $n'=n-1$.
--
--   The truncated $\chi^2$-divergence is thereby reduced to posterior second moments of the local interactions $\eta_k$ of bounded order.
--
--   **Formalization Note** In the regime (1), for every slack $B^*$. $\eta_k$ is placed on the first $k$ vertices and $\mathrm{Post}$ conditions on the whole graph $G_n$. The $o(1/n)$ is $e_n/n$ with $e_n\to0$ chosen after the sequences.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - generalization: B* a suitably large constant (in Δ) → every B* ∈ ℕ; reason: the proof uses only Propositions 3–4, which hold for every B* ≥ 0
--   - encoding: Post(η_k), o(1/n) → Post of η_k placed on the first k vertices; e_n/n with e → 0 after the sequences; reason: exchangeability makes the choice of k vertices immaterial; the paper's asymptotic notation
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Theorem 3, eq. (13), p.6 (PDF p.8)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_Delta
import Definitions.Def_RGGDetect_postMoment

open Filter Topology

namespace RGGDetect

/-- **Theorem 3** (Fourier reduction; arXiv:2610.08517, held version, sha256 e7bebd4a…, Theorem 3,
p.6, eq. (13)): for any fixed integer `K > 2/δ`, the quantity `Δ` of (9) satisfies
`Δ ≤ 2 ∑_{k=2}^{K-1} \binom{n′}{k} Post(η_k) + o(1/n)`, with `Post` defined by (5).

**Formalization Note** In the regime (1), for every slack `B*` (`B`). `η_k` is placed on the first `k`
vertices of the `n`-vertex configuration and `Post` conditions on the whole graph `G_n`. The `o(1/n)`
is `e_n/n` for a sequence `e → 0` chosen after the sequences. -/
theorem theorem_3 (δ : ℝ) (hδ : 0 < δ) (B K : ℕ) (hK : (K : ℝ) > 2 / δ) (p : ℕ → ℝ) (d : ℕ → ℕ)
    (τ : ℕ → ℝ) (hR : Regime δ p d τ) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      Delta n (d n) (τ n) B ≤
        2 * ∑ k ∈ Finset.Icc 2 (K - 1), ((n - 1).choose k : ℝ) *
          Post (τ n) (onFirst (n := n) k (eta (d n) (τ n) k)) + e n / n := by sorry

end RGGDetect
