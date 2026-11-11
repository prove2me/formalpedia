-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_lemma_3_3
-- name    : PriceIgnorance.Pairwise.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:14:24.713901+00:00
-- url     : https://prove2.me/theorems/ec8ae165-f09a-4f54-9a0e-191d91c7841d
-- title:
--   Lemma 3.3 — reduction of correlation-blind ratios to finitely supported marginals, losing a factor $1-\varepsilon$
-- statement:
--   Fix $k$ and $\varepsilon>0$, and let $D_1,\dots,D_n$ be non-degenerate marginals ($0<\max_i\mathbb E[V_i]<\infty$, values nonnegative). Then there are non-degenerate marginals $D'_1,\dots,D'_n$, each with finite support, with the following property. For every $\beta\ge0$: if some fixed-order online algorithm $B'$ satisfies
--   $$\mathbb E_{D'}[\mathrm{val}(B',V)]\ \ge\ \beta\,\mathbb E_{D'}\Big[\max_i V_i\Big]\qquad\text{for all }D'\in kI(D'_1,\dots,D'_n),$$
--   then some fixed-order online algorithm $B$ satisfies
--   $$\mathbb E_{D}[\mathrm{val}(B,V)]\ \ge\ \beta(1-\varepsilon)\,\mathbb E_{D}\Big[\max_i V_i\Big]\qquad\text{for all }D\in kI(D_1,\dots,D_n).$$
--   The same marginals $D'_1,\dots,D'_n$ also serve in uniformly random order (prophet secretary): the same implication holds with random-order online algorithms, $\mathrm{val}$ being averaged over a uniformly random arrival order independent of the values.
--
--   In words: a correlation-blind competitive ratio of $\beta$ given $D'_1,\dots,D'_n$ yields a correlation-blind competitive ratio of $\beta(1-\varepsilon)$ given $D_1,\dots,D_n$. This reduces Theorem 3.1 to finitely supported marginals, where the minimax theorem applies.
--
--   Differences from the source:
--   - encoding: marginals D_1..D_n with footnote 3 (0 < max_i E[V_i] < ∞, values ≥ 0) → NonDegenerate D_1..D_n; reason: footnote 3 is attached to the lemma; it only excludes undefined ratios
--   - reading: a competitive ratio β → β ≥ 0; reason: a competitive ratio is a ratio of nonnegative values; for β < 0 and ε > 1 the literal implication would ask for a ratio β(1 − ε) > 1
--   - encoding: a correlation-blind competitive ratio of β is possible given D' → ∃ B, ∀ D' ∈ kI(D'), β · E_{D'}[max_i V_i] ≤ E_{D'}[val(B,V)]; reason: multiplied out; the same since E_{D'}[max_i V_i] > 0 for non-degenerate D'
--   - reading: marginals D'_1..D'_n with finite supports → NonDegenerate D' with finite supports; reason: D' are marginals of the problem, so footnote 3's standing assumptions apply to them; the paper's D' = f(D) satisfies them
--   - reading: a correlation-blind competitive ratio (stated in the prophet (secretary) context of Theorem 3.1) → one D' and two clauses, for fixed order and for uniformly random order; reason: the proof of Theorem 3.1 uses the lemma for prophet secretary too, by overloading val (p. 7), and D' = f(D) does not depend on the arrival model
--   - encoding: online algorithms → OnlineAlg n / OnlineAlgRO n with behavioural stopping probabilities, measurable in the history; in random order σ is uniform on permutations of Fin n, independent of values and internal randomness, identities revealed, val averaged over σ; reason: same value functions as mixtures of deterministic rules (Kuhn); the standard prophet secretary model the paper uses
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 5, Lemma 3.3 and footnote 3 (proof p. 26)

import Mathlib
import Definitions.Def_PriceIgnorance_Pairwise_Instance
import Definitions.Def_PriceIgnorance_Pairwise_Algorithms
import Definitions.Def_PriceIgnorance_Pairwise_Ratios

open MeasureTheory

namespace PriceIgnorance.Pairwise

/-- Lemma 3.3 (p. 5): for `ε > 0` and non-degenerate marginals `D_1, …, D_n` there are
non-degenerate finitely supported marginals `D'_1, …, D'_n` such that, if one correlation-blind
algorithm achieves ratio `β ≥ 0` on every `D' ∈ kI(D'_1, …, D'_n)`, then one correlation-blind
algorithm achieves ratio `β(1 - ε)` on every `D ∈ kI(D_1, …, D_n)`; this holds both for the
prophet inequality (fixed order) and for the prophet secretary problem (uniformly random order,
`val` averaged over the order, as in the proof of Theorem 3.1, p. 7). -/
theorem lemma_3_3 (k : ℕ) (ε : ℝ) (hε : 0 < ε) {n : ℕ} (Dm : Fin n → Measure ℝ)
    (hDm : NonDegenerate Dm) :
    ∃ Dm' : Fin n → Measure ℝ, NonDegenerate Dm' ∧ (∀ i, HasFiniteSupport (Dm' i)) ∧
      (∀ β : ℝ, 0 ≤ β →
        (∃ B : OnlineAlg n, ∀ D' ∈ kI Dm' k, β * expMax D' ≤ expVal fixedOrder B D') →
        ∃ B : OnlineAlg n, ∀ D ∈ kI Dm k, β * (1 - ε) * expMax D ≤ expVal fixedOrder B D) ∧
      (∀ β : ℝ, 0 ≤ β →
        (∃ B : OnlineAlgRO n, ∀ D' ∈ kI Dm' k, β * expMax D' ≤ expVal randomOrder B D') →
        ∃ B : OnlineAlgRO n, ∀ D ∈ kI Dm k, β * (1 - ε) * expMax D ≤ expVal randomOrder B D) := by sorry

end PriceIgnorance.Pairwise
