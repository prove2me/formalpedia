-- Prove2me | Theorems.Thm_TemporalVoter_Supplement_theorem_4_7
-- name    : TemporalVoter.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:33:51.562851+00:00
-- url     : https://prove2.me/theorems/521333a3-a4de-466a-bdf6-bbb31ca8430b
-- title:
--   Theorem 4.7 — $d(x)$-regular temporal graphs with averaged conductance $\Theta(d(x)/x)$ on which the voter model does not absorb within $cx\Delta(x)/(d(x)\phi(x))$
-- statement:
--   This is the general lower-bound construction of Section 4, from which Theorem 1.4 and Main Theorem 2 follow.
--
--   For a temporal graph $\mathcal G$ with fixed degrees on vertex set $V$, write $\phi^t(S)=e_t(S,\overline S)/\mathrm{Vol}(S)$, and run the standard voter model $(\xi_t)_{t\ge0}$ on it.
--
--   **Theorem.** There is a constant $c>0$ with the following property. Let $d:\mathbb N\to\mathbb N$ be such that $d(x)$ is odd for every $x$ (so $d(x)\ge1$) and
--   $$
--   d(x)\le\frac{\sqrt x}{\log x}\qquad(x\ge2).
--   $$
--   Then there are $\phi:\mathbb N\to\mathbb R$ and $\Delta:\mathbb N\to\mathbb N$ with $\phi(x)=\Theta(d(x)/x)$ and $\Delta(x)=\Theta(x/d(x))$ as $x\to\infty$ (two-sided bounds with positive constants for all $x\ge N_0$) such that for infinitely many $x$ there is a temporal graph $\mathcal G$ on $n$ vertices with:
--
--   1. $\mathcal G$ is $d(x)$-regular and $x\le n\le 2x$;
--   2. for every time interval $I$ of length $\Delta(x)$ and every $S\subseteq V$ with $0<\mathrm{Vol}(S)\le\mathrm{Vol}(V)/2$, $\frac1{|I|}\sum_{t\in I}\phi^t(S)\ge\phi(x)$;
--   3. there is an initial minority set $s_0$, i.e. a two-opinion initial state, from which with probability at least $1/2$ the voter model does not absorb within time $\dfrac{c\,x\,\Delta(x)}{d(x)\,\phi(x)}$.
--
--   Here $\log$ is the natural logarithm.
--
--   **Formalization Note** The constant $c$ is chosen before the function $d$. "Infinitely many $x$" is "for every $N$ some $x\ge N$". The vertex set is $\{0,\dots,n-1\}$. $\mathrm{Vol}(V)/2=m$, and the averaged condition is the definition `windowAvgCond`.
--
--   Differences from the source:
--   - reading: 1 ≤ d(x) ≤ √x/log x for all x ∈ ℕ → d(x) odd for all x, and d(x) ≤ √x/log x for x ≥ 2; reason: √0/log 0 is undefined (and Lean's log 0 = 0 would make the hypothesis unsatisfiable, the theorem vacuous) and √1/log 1 = ∞ imposes nothing; oddness gives d(x) ≥ 1
--   - encoding: φ(x) = Θ(d(x)/x), Δ(x) = Θ(x/d(x)) as x → ∞ → ∃ C₁ C₂ > 0, ∃ N₀, ∀ x ≥ N₀, two-sided bounds; reason: the standard meaning of Θ for positive rates, made explicit
--   - encoding: an initial minority set s₀ ⊆ V(𝒢) → a two-opinion initial state σ₀; reason: every two-opinion state has a minority set and absorption is symmetric in the two opinions, so the two existentials are equivalent
--   - encoding: 0 < Vol(S) ≤ Vol(V(𝒢))/2 → 0 < Vol(S) ≤ m; reason: m = Vol(V)/2 by definition
--   - encoding: "for infinitely many values of x", an n-vertex graph → ∀ N, ∃ x ≥ N, a graph on Fin n; reason: Lean convention, same instances
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), §4, Theorem 4.7, p.32

import Mathlib
import Definitions.Def_TemporalVoter_voterLaw
import Definitions.Def_TemporalVoter_Supplement_windowAvgCond

open scoped ENNReal

namespace TemporalVoter

namespace Supplement

/-- **Theorem 4.7** (Rocha Avila, Dell, Lapinskas, *Temporal Conductance and Bounds on the Voter
Model for Dynamic Networks*, arXiv:2606.13374, version of 2 Nov 2026, §4, p.32): there is `c > 0`
such that, for every `d : ℕ → ℕ` with `d(x)` odd and `1 ≤ d(x) ≤ √x / log x`, there are
`φ : ℕ → ℝ` and `Δ : ℕ → ℕ` with `φ(x) = Θ(d(x)/x)` and `Δ(x) = Θ(x/d(x))` such that, for
infinitely many `x`, there is an `n`-vertex temporal graph `G` with
(i) `G` `d(x)`-regular and `x ≤ n ≤ 2x`;
(ii) `(1/|I|) ∑_{t ∈ I} φ^t(S) ≥ φ(x)` for every interval `I` of length `Δ(x)` and every `S` with
`0 < Vol(S) ≤ Vol(V)/2`;
(iii) an initial minority set `s₀` from which, with probability at least `1/2`, the standard voter
model on `G` does not absorb within time `cxΔ(x)/(d(x)φ(x))`.

**Formalization Note** `c` is chosen before the function `d`. The bound `d(x) ≤ √x / log x` is
required for `x ≥ 2` only: at `x = 0` the paper's `√0/log 0` is undefined (Lean's `Real.log 0 = 0`
would make the hypothesis unsatisfiable and the theorem vacuous), and at `x = 1` it is `1/0 = ∞`,
no constraint. Oddness gives `d(x) ≥ 1`. `Θ` is the two-sided bound with positive constants for
all `x ≥ N₀`. "Infinitely many `x`" is `∀ N, ∃ x ≥ N`; the vertex set is `Fin n`. An initial
minority set `s₀` is encoded as a two-opinion initial state `σ₀` (its minority set; absorption is
symmetric in the two opinions). `Vol(V)/2 = m`. "Does not absorb within time `X`": no time `t ≤ X`
is a consensus. -/
theorem theorem_4_7 : ∃ c : ℝ, 0 < c ∧
    ∀ d : ℕ → ℕ, (∀ x, Odd (d x)) →
      (∀ x : ℕ, 2 ≤ x → (d x : ℝ) ≤ Real.sqrt x / Real.log x) →
      ∃ (φ : ℕ → ℝ) (Δ : ℕ → ℕ),
        (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ N₀ : ℕ, ∀ x ≥ N₀,
          C₁ * d x / x ≤ φ x ∧ φ x ≤ C₂ * d x / x) ∧
        (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ N₀ : ℕ, ∀ x ≥ N₀,
          C₁ * x / d x ≤ (Δ x : ℝ) ∧ (Δ x : ℝ) ≤ C₂ * x / d x) ∧
        ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧ ∃ n : ℕ, ∃ T : TemporalGraph (Fin n),
          ((∀ v, T.d v = d x) ∧ x ≤ n ∧ n ≤ 2 * x) ∧
          windowAvgCond T (Δ x) (φ x) ∧
          ∃ σ₀ : Fin n → Fin 2, (1 / 2 : ℝ≥0∞) ≤ voterLaw T 2 σ₀
            {ω | ∀ t : ℕ, (t : ℝ) ≤ c * x * Δ x / (d x * φ x) → ¬ IsConsensus (ω t)} := by sorry

end Supplement

end TemporalVoter
