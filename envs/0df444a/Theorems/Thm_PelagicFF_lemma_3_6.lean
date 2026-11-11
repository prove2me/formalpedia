-- Prove2me | Theorems.Thm_PelagicFF_lemma_3_6
-- name    : PelagicFF.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:57.153948+00:00
-- url     : https://prove2.me/theorems/20757958-6e9f-4027-9d73-9381fdc2f801
-- title:
--   Lemma 3.6 — window bound $\Pr[a\le|A+S+\mathrm{err}|\le3a]\le p^*$ for large $s$
-- statement:
--   For each positive integer $s$ let $T=A+S+\mathrm{err}$, where $A$ and $S$ are independent, $S$ is distributed as $s^{-1/2}\sum_{i=1}^s\xi_i$ for independent uniform signs $\xi_i\in\{-1,1\}$, and $\mathbb E[\mathrm{err}^2]=o(1)$ as $s\to\infty$; $\mathrm{err}$ may depend on $A$ and $S$. Then for all sufficiently large $s$,
--   $$\Pr\big[a\le|T|\le3a\big]\ \le\ p^*,$$
--   where $a=\sqrt{2/3}$ and $p^*=0.6$.
--
--   Combined with Lemma 4.3 it shows that on every non-rare transcript Bob's coefficient lands in the window with probability at most $0.6<2/3$.
--
--   **Formalization Note** Sequence form: positive integers $s_j\to\infty$, one probability space per index with real random variables $A_j$ (arbitrary), $S_j$, $\mathrm{err}_j$; "for all sufficiently large $s$" is "for all sufficiently large $j$". $\mathbb E[\mathrm{err}^2]$ is a lower Lebesgue integral.
--
--   Differences from the source:
--   - generalization: one instance for each positive integer s, s → ∞ → any sequence of positive integers s_j → ∞ with one instance per j; conclusion eventually in j; reason: s_j = j + 1 gives the paper's form
--   - encoding: random variables A, S, err → measurable real functions on a probability space; reason: standing convention that random variables are measurable
--   - encoding: E[err²] → ∫⁻ ofReal(err²); reason: equals the expectation of the nonnegative err²; no integrability junk
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.6, p.23

import Mathlib
import Definitions.Def_PelagicFF_rademacherLaw

open MeasureTheory ProbabilityTheory Filter Topology

namespace PelagicFF

/-- **Lemma 3.6.** For each positive integer `s` let `T = A + S + err`, where `A` and `S` are
independent, `S` is distributed as `s^{−1/2} ∑ᵢ ξᵢ` for independent uniform signs, and
`E[err²] = o(1)` as `s → ∞`; `err` may depend on `A` and `S`. Then for all sufficiently large `s`,
`Pr[a ≤ |T| ≤ 3a] ≤ p∗`, with `a = √(2/3)` and `p∗ = 0.6` (Fact 3.5).

arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.6, p.23.

**Formalization Note.** Sequence form: positive integers `s j → ∞`, a probability space `Ω_j` per
index, and "for all sufficiently large `s`" is `∀ᶠ j in atTop` (the paper's form is `s j = j + 1`).
`A` is any real random variable; `E[err²]` is a lower Lebesgue integral. -/
theorem lemma_3_6 (s : ℕ → ℕ) (hs : Tendsto s atTop atTop) (hpos : ∀ j, 0 < s j)
    (Ω : ℕ → Type) [∀ j, MeasurableSpace (Ω j)] (P : ∀ j, Measure (Ω j))
    [∀ j, IsProbabilityMeasure (P j)] (A S err : ∀ j, Ω j → ℝ)
    (hA : ∀ j, Measurable (A j)) (hS : ∀ j, Measurable (S j)) (herrm : ∀ j, Measurable (err j))
    (hind : ∀ j, IndepFun (A j) (S j) (P j))
    (hlaw : ∀ j, (P j).map (S j) = rademacherLaw (s j))
    (herr : Tendsto (fun j => ∫⁻ ω, ENNReal.ofReal (err j ω ^ 2) ∂(P j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, P j {ω | Real.sqrt (2 / 3) ≤ |A j ω + S j ω + err j ω| ∧
      |A j ω + S j ω + err j ω| ≤ 3 * Real.sqrt (2 / 3)} ≤ ENNReal.ofReal (3 / 5) := by sorry

end PelagicFF
