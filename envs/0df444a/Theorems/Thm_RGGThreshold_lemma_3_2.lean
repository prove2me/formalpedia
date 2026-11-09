-- Prove2me | Theorems.Thm_RGGThreshold_lemma_3_2
-- name    : RGGThreshold.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:01:25.88921+00:00
-- url     : https://prove2.me/theorems/7c789e8a-6132-419f-b428-22173a4c18c0
-- title:
--   Lemma 3.2 — $G(n,d,p)\in\mathcal D$ with probability at least $1-\varepsilon$
-- statement:
--   For every $\varepsilon>0$ there exists $K^{\mathcal D}>0$, which may depend on $\varepsilon$, such that the following holds. Let $G\sim G(n,d,p)$ with $d\ge Cn^3p^3(\log p^{-1})^3$ and $n^{-1/5}(\log n)^A\le p\le1/3$, for $C$ sufficiently large compared to $K^{\mathcal D}$. Then
--
--   $$
--   \mathbb P[G\in\mathcal D]\ge1-\varepsilon .
--   $$
--
--   Above the threshold the random geometric graph has typical signed counts of triangles, four-cycles and diamonds, so the correction terms of Proposition 2.1 are small.
--
--   **Formalization Note** $A$ is the large absolute constant of Theorem 1.2 and is chosen first. "$C$ sufficiently large compared to $K^{\mathcal D}$" is $\exists C>0$ after $K^{\mathcal D}$; the conclusion is monotone in $C$. The printed lemma does not ask for $n$ large, and the Lean statement does not either. The law of $G(n,d,p)$ is the published `RGGDetect.rggLaw`.
--
--   Differences from the source:
--
--   - reading: A from the context (the large absolute constant of Theorem 1.2) → ∃ A first, before ε; reason: A is absolute
--   - reading: "for C sufficiently large compared to K^𝒟" → ∃ C > 0 after K^𝒟; reason: the event and the hypothesis are monotone in C, so this is the same as ∀ C ≥ C₀
--   - reading: p "a probability" → 0 < p; reason: p ∈ (0, 1) as in Theorem 1.2; p ≤ 1/3 is stated
--   - encoding: A a large absolute (real) constant → A : ℕ, used as (log n)^A; reason: for n ≥ 3, raising A to ⌈A⌉ only shrinks the p-range, so the two forms are equivalent
--   - encoding: the threshold c_{p,d}/√d with P[⟨x_i,x_j⟩ ≥ c_{p,d}/√d] = p → any τ with capProb d τ = p; reason: for d ≥ 2 this τ is unique and equals c_{p,d}/√d; the Lean statement holds for every solution
--   - encoding: vertices and coordinates 1, …, n → Fin n, numbered from 0; reason: index shift only; each statement shifts s accordingly
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 3.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_RGGDetect_rggLaw
import Definitions.Def_RGGThreshold_InD

open MeasureTheory

namespace RGGThreshold

/-- **Lemma 3.2** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Lemma 3.2, p.10 (PDF p.12)). For every `ε > 0` there exists `K^𝒟 > 0`,
which may depend on `ε`, such that: if `G ∼ G(n, d, p)` with `d ≥ C n³p³(log p⁻¹)³` and
`n^{-1/5}(log n)^A ≤ p ≤ 1/3`, for `C` sufficiently large compared to `K^𝒟`, then `P[G ∈ 𝒟] ≥ 1 - ε`.

**Formalization Note** `A` is the large absolute constant of Theorem 1.2, chosen first; "`C`
sufficiently large compared to `K^𝒟`" is `∃ C > 0` after `K^𝒟` (the conclusion is monotone in
`C`). The printed lemma has no "`n` large", and none is added. `p` is a probability, `0 < p`.
`G(n, d, p)` is `RGGDetect.rggLaw n d τ` for any `τ` with `P[⟨x_1, x_2⟩ ≥ τ] = p`. -/
theorem lemma_3_2 :
    ∃ A : ℕ, ∀ ε : ℝ, 0 < ε → ∃ KD : ℝ, 0 < KD ∧ ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ p : ℝ, 0 < p → (n : ℝ) ^ (-(1 / 5 : ℝ)) * Real.log n ^ A ≤ p → p ≤ 1 / 3 →
    ∀ d : ℕ, C * (n : ℝ) ^ 3 * p ^ 3 * Real.log (1 / p) ^ 3 ≤ d →
    ∀ τ : ℝ, RGGDetect.capProb d τ = p →
    1 - ε ≤ (RGGDetect.rggLaw n d τ).real {H | InD KD n p H} := by sorry

end RGGThreshold
