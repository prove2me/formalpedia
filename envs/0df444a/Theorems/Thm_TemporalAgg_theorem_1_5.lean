-- Prove2me | Theorems.Thm_TemporalAgg_theorem_1_5
-- name    : TemporalAgg.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:08.971387+00:00
-- url     : https://prove2.me/theorems/dab3d311-67c1-4834-965b-6e2dac042b80
-- title:
--   Theorem 1.5 — Greedy Temporal Aggregation: load ≤ (log₂ n + 1)L w.p. 1 − ε(T+1), at most q(log_{3/2} n + 5) samples
-- statement:
--   Let $f$ be a load function on $\mathcal U^n$.
--
--   1. **GTA is well defined.** For every sequence of adversarial sample sets $(A_t)_{t\ge1}$ there is a run of Greedy Temporal Aggregation.
--   2. **Samples.** Under every run and for every horizon $T$, if the adversary performs $q=\sum_{t=1}^{T}|A_t|$ samples, GTA performs at most $q(\log_{3/2} n+5)$ samples.
--   3. **Load.** Suppose that at every time step $t\le T$ the static realization satisfies $f(\mathcal S^t)\le L$ with probability at least $1-\varepsilon$. Then, under GTA, with probability at least $1-\varepsilon(T+1)$,
--
--   $$
--   f(\mathcal R^t)\le(\log_2 n+1)\,L\qquad\text{at all times } t\le T\text{ simultaneously.}
--   $$
--
--   In clause 3, $(\Omega,\mu)$ is a probability space, the static realizations $\mathcal S^t$, the adversarial sets and the GTA run are random and may depend on each other arbitrarily, and $\mathcal R^t_u=\mathcal S^{\mathrm{last}_t(u)}_u$; the conclusion is $\mu\{\exists t\le T: (\log_2 n+1)L<f(\mathcal R^t)\}\le(T+1)\varepsilon$.
--
--   So every static high-probability load guarantee is kept, against an adaptive adversary, within a logarithmic factor at all times, at a logarithmic factor in samples. Clauses 2 and 3 are Lemmas 3.3 and 3.2, which the paper says together constitute the theorem.
--
--   **Formalization Note** $\log_2$ and $\log_{3/2}$ are `Real.logb 2` and `Real.logb (3/2)`. Bad events are measured by $\mu$ as an outer measure in $[0,\infty]$; no measurability is assumed, and $L,\varepsilon$ are unconstrained.
--
--   Differences from the source:
--   - reading: f(ℛᵗ) ≤ L · O(log n); at most q · O(log n) samples → f(ℛᵗ) ≤ (log₂ n + 1)·L and at most q·(log_{3/2} n + 5) samples, for every n; reason: these are the constants of the proof (Lemmas 3.2 and 3.3, which 'together constitute Theorem 1.5', p.17); they imply the O-form, and at n = 1 a literal C·log n bound would be false
--   - generalization: the adaptive process of §1.2 (p.3): adversarial distributions and samples, static realization 𝒮ᵗ, joint realization ℛᵗ → any probability space (Ω, μ), any random vectors S t, any random adversarial sets A and GTA runs last, alg for A(ω); ℛᵗ_u = S (last ω t u) ω u; reason: in the paper's process let every sample taken at time s be coordinate u of one fresh vector 𝒮ˢ drawn from the product of the time-s distributions (the splice used in the proof of Lemma 3.2, p.16); then ℛᵗ is this splice and the paper's hypothesis is the Lean hypothesis; no independence or adaptedness is assumed, so every adaptive adversary is covered
--   - generalization: Greedy Temporal Aggregation, with the merged pair (t₁, t₂) left unspecified → every run of the nondeterministic relation IsGTARun (any choice of candidate pair at every iteration); reason: any deterministic or randomized choice rule produces such a run, so the statement specializes to each
--   - generalization: Greedy Temporal Aggregation is well defined ('so the loop terminates', p.16) → an extra first clause: for every sequence of adversarial sample sets a GTA run exists; reason: it makes the every-run clauses non-vacuous and is implied by the termination sentence of p.16; dropping it gives the paper's two claims
--   - reading: while there exist time steps t₁ ≠ t₂ whose groups differ in size by at most a factor of 2 (Algorithm 1, p.16) → both groups nonempty, sizes a, b with a ≤ 2b and b ≤ 2a; reason: two empty groups would satisfy the condition forever, contradicting 'so the loop terminates' and 'the sizes of any two nonempty groups differ by more than a factor of 2' (p.16)
--   - encoding: f(𝒮ᵗ) ≤ L with probability at least 1 − ε; with probability at least 1 − ε(T+1), f(ℛᵗ) ≤ … at all t ≤ T → μ{ω | L < f(S t ω)} ≤ ε and μ{ω | ∃ t ≤ T, … < f(ℛᵗ ω)} ≤ (T+1)·ε in ℝ≥0∞, μ as an outer measure, no measurability hypotheses; reason: for measurable events and a probability measure the two forms are equivalent; ε and L are unconstrained, which covers ε ∈ [0, 1]
--   - encoding: f : 𝒰ⁿ → ℝ≥0 (Definition 1.1) → f : (Fin n → U) → ℝ satisfying the splice inequality; reason: the splice inequality with x = y = z gives f ≥ 0, so the instances are the same
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), Theorem 1.5, p.7 (proof: Lemmas 3.2 and 3.3, pp.16–17)

import Mathlib
import Definitions.Def_TemporalAgg_IsLoadFunction
import Definitions.Def_TemporalAgg_IsGTARun
import Definitions.Def_TemporalAgg_jointRealization

open MeasureTheory
open scoped ENNReal

namespace TemporalAgg

/-- **Theorem 1.5** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive
Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.7), with the constants of its proof ("Together, Lemmas 3.2 and 3.3
constitute Theorem 1.5", p.17).

Let `f` be a load function on `𝒰ⁿ`.
1. For every sequence of adversarial sample sets there is a run of Greedy Temporal Aggregation
   (the loop terminates at every step).
2. Under every GTA run, for every horizon `T`, if the adversary performs `q = ∑_{t=1}^{T} |A_t|`
   samples, GTA performs at most `q·(log_{3/2} n + 5)` samples.
3. If at every time `t ≤ T` the static realization satisfies `f(𝒮ᵗ) ≤ L` with probability at
   least `1 − ε`, then under GTA, with probability at least `1 − ε(T+1)`, the joint realization
   satisfies `f(ℛᵗ) ≤ (log₂ n + 1)·L` at all times `t ≤ T` simultaneously.

**Formalization Note** Clauses 2 and 3 coincide with Lemmas 3.3 and 3.2 (separate items of the
mission); clause 1 makes the "every run" clauses non-vacuous. The constants `log₂ n + 1` and
`log_{3/2} n + 5` replace the page's `O(log n)` (they are what the proof gives; at `n = 1` a
literal `C·log n` would be false). GTA is the nondeterministic relation `IsGTARun`: every choice
of merge pair is covered. The probabilistic model is generalized as in Lemma 3.2: any probability
space, any random static vectors `S`, any random adversarial sets and GTA runs, with `ℛᵗ` the
splice `jointRealization`; the paper's adaptive process is the instance where every sample
taken at time `s` is a coordinate of one fresh vector `𝒮ˢ`. Bad events are measured by `μ`
as an outer measure in `ℝ≥0∞`; no measurability is assumed; `L`, `ε` are unconstrained. -/
theorem theorem_1_5 {U : Type*} {n : ℕ} (f : (Fin n → U) → ℝ) (hf : IsLoadFunction f)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (∀ A : ℕ → Finset (Fin n), ∃ (last : ℕ → Fin n → ℕ) (alg : ℕ → ℕ), IsGTARun A last alg) ∧
    (∀ (A : ℕ → Finset (Fin n)) (last : ℕ → Fin n → ℕ) (alg : ℕ → ℕ), IsGTARun A last alg →
      ∀ T : ℕ, (∑ t ∈ Finset.Icc 1 T, (alg t : ℝ)) ≤
        (∑ t ∈ Finset.Icc 1 T, ((A t).card : ℝ)) * (Real.logb (3 / 2) n + 5)) ∧
    (∀ (S : ℕ → Ω → Fin n → U) (A : Ω → ℕ → Finset (Fin n)) (last : Ω → ℕ → Fin n → ℕ)
      (alg : Ω → ℕ → ℕ) (L : ℝ) (ε : ℝ≥0∞) (T : ℕ),
      (∀ ω, IsGTARun (A ω) (last ω) (alg ω)) →
      (∀ t ≤ T, μ {ω | L < f (S t ω)} ≤ ε) →
      μ {ω | ∃ t ≤ T, (Real.logb 2 n + 1) * L < f (jointRealization S last ω t)} ≤
        ((T : ℝ≥0∞) + 1) * ε) := by sorry

end TemporalAgg
