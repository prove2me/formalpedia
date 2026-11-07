-- Prove2me | Theorems.Thm_TemporalAgg_lemma_3_2
-- name    : TemporalAgg.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:16.179069+00:00
-- url     : https://prove2.me/theorems/2b5cb9e2-bd83-4ee5-ac3a-2eeeaedb32a7
-- title:
--   Lemma 3.2 — GTA keeps f(ℛᵗ) ≤ (log₂ n + 1)L at all t ≤ T w.p. 1 − ε(T+1)
-- statement:
--   Let $f$ be a load function. Suppose that at every time step $t\le T$ the static realization satisfies $f(\mathcal S^t)\le L$ with probability at least $1-\varepsilon$. Then, under Greedy Temporal Aggregation, with probability at least $1-\varepsilon(T+1)$ the joint realization satisfies
--
--   $$
--   f(\mathcal R^t)\le(\log_2 n+1)\,L\qquad\text{at all times } t\le T \text{ simultaneously.}
--   $$
--
--   Precisely: let $(\Omega,\mu)$ be a probability space, $\mathcal S^t:\Omega\to\mathcal U^n$ random vectors, and for every $\omega$ let $(A_t(\omega))$ be adversarial sample sets and $(\mathrm{last}(\omega),\mathrm{alg}(\omega))$ a GTA run against them, with $\mathcal R^t_u(\omega)=\mathcal S^{\mathrm{last}_t(u)(\omega)}_u(\omega)$. If $\mu\{L<f(\mathcal S^t)\}\le\varepsilon$ for every $t\le T$, then
--
--   $$
--   \mu\bigl\{\exists\, t\le T:\ (\log_2 n+1)L<f(\mathcal R^t)\bigr\}\le (T+1)\,\varepsilon .
--   $$
--
--   This is the load half of Theorem 1.5: a static high-probability bound survives an adaptive adversary up to a logarithmic factor.
--
--   **Formalization Note** The sets $\mathcal S$, $A$ and the run may depend on $\omega$ in any way. $\mu$ is applied to the bad events as an outer measure, in $[0,\infty]$, so no measurability is assumed; $L$ and $\varepsilon$ are unconstrained.
--
--   Differences from the source:
--   - generalization: the adaptive process of §1.2 (p.3): adversarial distributions and samples, static realization 𝒮ᵗ, joint realization ℛᵗ → any probability space (Ω, μ), any random vectors S t, any random adversarial sets A and GTA runs last, alg for A(ω); ℛᵗ_u = S (last ω t u) ω u; reason: in the paper's process let every sample taken at time s be coordinate u of one fresh vector 𝒮ˢ drawn from the product of the time-s distributions (the splice used in the proof of Lemma 3.2, p.16); then ℛᵗ is this splice and the paper's hypothesis is the Lean hypothesis; no independence or adaptedness is assumed, so every adaptive adversary is covered
--   - generalization: Greedy Temporal Aggregation, with the merged pair (t₁, t₂) left unspecified → every run of the nondeterministic relation IsGTARun (any choice of candidate pair at every iteration); reason: any deterministic or randomized choice rule produces such a run, so the statement specializes to each
--   - reading: while there exist time steps t₁ ≠ t₂ whose groups differ in size by at most a factor of 2 (Algorithm 1, p.16) → both groups nonempty, sizes a, b with a ≤ 2b and b ≤ 2a; reason: two empty groups would satisfy the condition forever, contradicting 'so the loop terminates' and 'the sizes of any two nonempty groups differ by more than a factor of 2' (p.16)
--   - encoding: f(𝒮ᵗ) ≤ L with probability at least 1 − ε; with probability at least 1 − ε(T+1), f(ℛᵗ) ≤ … at all t ≤ T → μ{ω | L < f(S t ω)} ≤ ε and μ{ω | ∃ t ≤ T, … < f(ℛᵗ ω)} ≤ (T+1)·ε in ℝ≥0∞, μ as an outer measure, no measurability hypotheses; reason: for measurable events and a probability measure the two forms are equivalent; ε and L are unconstrained, which covers ε ∈ [0, 1]
--   - encoding: f : 𝒰ⁿ → ℝ≥0 (Definition 1.1) → f : (Fin n → U) → ℝ satisfying the splice inequality; reason: the splice inequality with x = y = z gives f ≥ 0, so the instances are the same
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), Lemma 3.2, p.16

import Mathlib
import Definitions.Def_TemporalAgg_IsLoadFunction
import Definitions.Def_TemporalAgg_IsGTARun
import Definitions.Def_TemporalAgg_jointRealization

open MeasureTheory
open scoped ENNReal

namespace TemporalAgg

/-- **Lemma 3.2** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive
Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.16).

Let `f` be a load function. Suppose that at every time step `t ≤ T` the static realization
satisfies `f(𝒮ᵗ) ≤ L` with probability at least `1 − ε`. Then, under GTA, with probability at
least `1 − ε·(T+1)`, the joint realization satisfies `f(ℛᵗ) ≤ (log₂ n + 1) L` at all times
`t ≤ T` simultaneously.

**Formalization Note** The probabilistic model is generalized: `(Ω, μ)` is any probability
space, `S t ω` any random vectors (the static realizations), `A ω` any random adversarial sets
and `last ω, alg ω` any GTA run for `A ω`; the joint realization is the splice
`ℛᵗ_u = 𝒮^{last ω t u}_u` (`jointRealization`). No independence, adaptedness or measurability
is assumed. The paper's adaptive process is the instance in which every sample taken at time `s`
is coordinate `u` of one fresh vector `𝒮ˢ` from the product of the time-`s` distributions,
so the paper's hypothesis is the hypothesis here. Probabilities are stated on the bad events, in
`ℝ≥0∞`, with `μ` read as an outer measure; for measurable events, `μ{L < f(𝒮ᵗ)} ≤ ε` is
`P(f(𝒮ᵗ) ≤ L) ≥ 1 − ε`. `L` and `ε` are unconstrained. -/
theorem lemma_3_2 {U : Type*} {n : ℕ} (f : (Fin n → U) → ℝ) (hf : IsLoadFunction f)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → Fin n → U) (A : Ω → ℕ → Finset (Fin n)) (last : Ω → ℕ → Fin n → ℕ)
    (alg : Ω → ℕ → ℕ) (L : ℝ) (ε : ℝ≥0∞) (T : ℕ)
    (hrun : ∀ ω, IsGTARun (A ω) (last ω) (alg ω))
    (hstatic : ∀ t ≤ T, μ {ω | L < f (S t ω)} ≤ ε) :
    μ {ω | ∃ t ≤ T, (Real.logb 2 n + 1) * L < f (jointRealization S last ω t)} ≤
      ((T : ℝ≥0∞) + 1) * ε := by sorry

end TemporalAgg
