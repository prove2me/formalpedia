-- Prove2me | Theorems.Thm_TemporalVoter_Supplement_theorem_1_4
-- name    : TemporalVoter.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:33:17.507215+00:00
-- url     : https://prove2.me/theorems/2877b7e0-cc85-43da-a0ec-33e34b8fb0d0
-- title:
--   Theorem 1.4 — high window-averaged conductance does not give consensus within $o(n\Delta(n)/(d\phi(n)))$
-- statement:
--   This lower bound shows that requiring a high *average* conductance over every window, instead of a high maximum, does not remove the dependence of the consensus time on the window length.
--
--   For a temporal graph $\mathcal G$ with fixed degrees, write $\phi^t(S)=e_t(S,\overline S)/\mathrm{Vol}(S)$ and $m$ for its number of edges, and run the standard voter model $(\xi_t)_{t\ge0}$ on it.
--
--   **Theorem.** There is a constant $c>0$ such that for every odd natural number $d$ there are functions $\phi:\mathbb N\to\mathbb R$ and $\Delta:\mathbb N\to\mathbb N$ with $\phi(n)=\Theta(1/n)$ and $\Delta(n)=\Theta(n)$ as $n\to\infty$, i.e. for some $C_1,C_2>0$ and $N_0$,
--   $$
--   \frac{C_1}{n}\le\phi(n)\le\frac{C_2}{n},\qquad C_1 n\le\Delta(n)\le C_2 n\qquad(n\ge N_0),
--   $$
--   such that for every $N$ there are $n\ge N$ and a $d$-regular temporal graph $\mathcal G$ on $n$ vertices with:
--
--   1. for every time interval $I$ of length $\Delta(n)$ and every $S\subseteq V$ with $0<\mathrm{Vol}(S)\le m$, $\frac{1}{|I|}\sum_{t\in I}\phi^t(S)\ge\phi(n)$;
--   2. from some initial state $\xi_0$ (with two opinions), with probability at least $1/2$ the voter model does not absorb within time $\dfrac{c\,n\,\Delta(n)}{d\,\phi(n)}$, i.e. no $t\le c\,n\,\Delta(n)/(d\,\phi(n))$ has $\xi_t$ constant.
--
--   Since $\phi(n)=\Theta(1/n)$ and $\Delta(n)=\Theta(n)$, the non-absorption time is of order $n^3/d$, although every window of length $\Theta(n)$ has average conductance $\Theta(1/n)$.
--
--   **Formalization Note** The constant $c$ is chosen before $d$; $\phi$ and $\Delta$ may depend on $d$. The vertex set is $\{0,\dots,n-1\}$. The window-averaged condition is the definition `windowAvgCond`.
--
--   Differences from the source:
--   - reading: "for all odd integers d" (a degree) → every odd natural number d; reason: d is the degree of a d-regular graph, so it is a positive integer
--   - encoding: φ(n) = Θ(1/n), Δ(n) = Θ(n) as n → ∞ → ∃ C₁ C₂ > 0, ∃ N₀, ∀ n ≥ N₀, two-sided bounds; reason: the standard meaning of Θ for positive rates, made explicit
--   - reading: "from some initial state" → an initial state with two opinions (Fin 2); reason: the paper's construction starts from a minority set (two opinions); the Lean statement implies the one with an unspecified number of opinions
--   - encoding: "arbitrarily large n-vertex" → ∀ N, ∃ n ≥ N, a graph on Fin n; reason: Lean convention, same instances
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Theorem 1.4, pp.7–8 (restated with proof p.33)

import Mathlib
import Definitions.Def_TemporalVoter_voterLaw
import Definitions.Def_TemporalVoter_Supplement_windowAvgCond

open scoped ENNReal

namespace TemporalVoter

namespace Supplement

/-- **Theorem 1.4 (Lower bound)** (Rocha Avila, Dell, Lapinskas, *Temporal Conductance and Bounds on
the Voter Model for Dynamic Networks*, arXiv:2606.13374, version of 2 Nov 2026, p.7, restated
p.33): there is `c > 0` such that for every odd `d` there are `φ : ℕ → ℝ` and `Δ : ℕ → ℕ` with
`φ(n) = Θ(1/n)` and `Δ(n) = Θ(n)` such that there are arbitrarily large `n`-vertex `d`-regular
temporal graphs `G` with
(i) `(1/|I|) ∑_{t ∈ I} φ^t(S) ≥ φ(n)` for every interval `I` of length `Δ(n)` and every `S` with
`0 < Vol(S) ≤ m`, and
(ii) from some initial state, with probability at least `1/2`, the standard voter model on `G` does
not absorb within time `cnΔ(n)/(dφ(n))`.

**Formalization Note** `c` is chosen before `d`; `φ`, `Δ` may depend on `d`. "Odd integers `d`"
are the odd naturals (a degree). `f(n) = Θ(g(n))` is the two-sided bound
`C₁ g(n) ≤ f(n) ≤ C₂ g(n)` for all `n ≥ N₀`, with `C₁, C₂ > 0` (so `φ` is eventually positive).
"Arbitrarily large" is `∀ N, ∃ n ≥ N`; the vertex set is `Fin n`. The initial state is a
two-opinion state. "Does not absorb within time `X`": no time `t ≤ X` is a consensus. -/
theorem theorem_1_4 : ∃ c : ℝ, 0 < c ∧
    ∀ d : ℕ, Odd d →
      ∃ (φ : ℕ → ℝ) (Δ : ℕ → ℕ),
        (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
          C₁ / n ≤ φ n ∧ φ n ≤ C₂ / n) ∧
        (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
          C₁ * n ≤ (Δ n : ℝ) ∧ (Δ n : ℝ) ≤ C₂ * n) ∧
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ T : TemporalGraph (Fin n),
          (∀ v, T.d v = d) ∧
          windowAvgCond T (Δ n) (φ n) ∧
          ∃ σ₀ : Fin n → Fin 2, (1 / 2 : ℝ≥0∞) ≤ voterLaw T 2 σ₀
            {ω | ∀ t : ℕ, (t : ℝ) ≤ c * n * Δ n / (d * φ n) → ¬ IsConsensus (ω t)} := by sorry

end Supplement

end TemporalVoter
