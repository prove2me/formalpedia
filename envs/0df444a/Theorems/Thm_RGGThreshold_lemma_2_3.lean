-- Prove2me | Theorems.Thm_RGGThreshold_lemma_2_3
-- name    : RGGThreshold.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:59.260583+00:00
-- url     : https://prove2.me/theorems/104fcb3c-d3e6-4abf-8d24-c0c75d513d21
-- title:
--   Lemma 2.3 — $G(n,d,p)\in\mathcal E$ with probability $1-o(1)$
-- statement:
--   There exist absolute constants $K^{\mathcal E},C$ such that for $1/3\ge p\ge n^{-1/3}\,\mathrm{polylog}(n)$ and $d\ge Cn^2p\,\mathrm{polylog}(n)$,
--
--   $$
--   \mathbb P\big[G(n,d,p)\in\mathcal E\big]=1-o(1)\qquad(n\to\infty).
--   $$
--
--   So the pseudorandomness assumptions of the main estimate cost only a vanishing probability.
--
--   **Formalization Note** $\mathrm{polylog}(n)$ is $(\log n)^B$ for one constant $B$; $1-o(1)$ means: for every $\eta>0$ there is $N$ such that the probability is at least $1-\eta$ for all $n\ge N$ and all admissible $p,d,\tau$. The law of $G(n,d,p)$ is the published `RGGDetect.rggLaw`.
--
--   Differences from the source:
--
--   - reading: polylog(n), twice → (log n)^B with one natural exponent B for both; reason: taking the larger exponent gives an equivalent statement for n ≥ 3
--   - reading: 1 − o(1) as n → ∞ → ∀ η > 0, ∃ N, ∀ n ≥ N and all admissible p, d, τ: probability ≥ 1 − η; reason: uniform over the parameter ranges, equivalent to the statement for every choice of sequences p(n), d(n)
--   - encoding: the threshold c_{p,d}/√d with P[⟨x_i,x_j⟩ ≥ c_{p,d}/√d] = p → any τ with capProb d τ = p; reason: for d ≥ 2 this τ is unique and equals c_{p,d}/√d; the Lean statement holds for every solution
--   - encoding: vertices and coordinates 1, …, n → Fin n, numbered from 0; reason: index shift only; each statement shifts s accordingly
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 2.3, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_RGGDetect_rggLaw
import Definitions.Def_RGGThreshold_InE

open MeasureTheory

namespace RGGThreshold

/-- **Lemma 2.3** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Lemma 2.3, p.9 (PDF p.11)). There exist absolute constants `K^𝓔, C` such
that for `1/3 ≥ p ≥ n^{-1/3} polylog(n)` and `d ≥ C n² p polylog(n)` we have
`P[G(n, d, p) ∈ 𝓔] = 1 - o(1)` as `n → ∞`.

**Formalization Note** `polylog(n)` is `(log n)^B` for a constant `B` (one `B` for both
occurrences). `1 - o(1)` as `n → ∞` is: for every `η > 0` there is `N` such that for all `n ≥ N`
and all admissible `p, d` the probability is at least `1 - η`. `G(n, d, p)` is the law
`RGGDetect.rggLaw n d τ` for any `τ` with `P[⟨x_1, x_2⟩ ≥ τ] = p`. -/
theorem lemma_2_3 :
    ∃ (K C : ℝ) (B : ℕ), 0 < K ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : ℝ, (n : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log n ^ B ≤ p → p ≤ 1 / 3 →
    ∀ d : ℕ, C * (n : ℝ) ^ 2 * p * Real.log n ^ B ≤ d →
    ∀ τ : ℝ, RGGDetect.capProb d τ = p →
    1 - η ≤ (RGGDetect.rggLaw n d τ).real {H | InE K n p H} := by sorry

end RGGThreshold
