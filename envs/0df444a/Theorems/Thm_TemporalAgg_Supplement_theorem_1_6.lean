-- Prove2me | Theorems.Thm_TemporalAgg_Supplement_theorem_1_6
-- name    : TemporalAgg.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:20:20.427636+00:00
-- url     : https://prove2.me/theorems/75f236ef-3b78-4028-b03d-05f2ff1805b0
-- title:
--   Theorem 1.6 — Aligned Temporal Aggregation: load factor $\log_\alpha T+2$, $\alpha(\log_\alpha T+1)$ samples per adversarial sample
-- statement:
--   Let $f$ be a load function on $\mathcal U^n$ and let $\alpha\ge2$ be an integer. Suppose that at every time step $t\le T$ the static realization satisfies $f(\mathcal S^t)\le L$ with probability at least $1-\varepsilon$. Then, under Aligned Temporal Aggregation with parameter $\alpha$:
--
--   1. with probability at least $1-\varepsilon(T+1)$, the joint realization satisfies
--   $$
--   f(\mathcal R^t)\le L\cdot(\log_\alpha T+2)\quad\text{at all times } t\le T \text{ simultaneously};
--   $$
--   2. for any fixed time $t\le T$, this bound $f(\mathcal R^t)\le L(\log_\alpha T+2)$ holds with probability at least $1-\varepsilon(\log_\alpha t+2)$;
--   3. if the adversary performs $q=\sum_{t=1}^{T}|A_t|$ samples, ATA performs at most $q\cdot\alpha(\log_\alpha T+1)$ samples.
--
--   The parameter $\alpha$ trades samples for load: for instance $\alpha=\lceil n^\delta\rceil$ gives a constant load factor with $O(n^\delta)$ samples per adversarial sample. Here $\mathcal R^t_u=\mathcal S^{\mathrm{last}_t(u)}_u$, where $\mathrm{last}_t(u)$ is the time step at which ATA's current realization of $u$ was sampled.
--
--   **Formalization Note** The probabilistic model is that of the mission's goal (Theorem 1.5): any probability space, random static vectors and random adversarial sample sets, with bad events measured as outer measures in $[0,\infty]$; $L$ and $\varepsilon$ are unconstrained. Logarithms are real, with $\log_\alpha 0$ read as $0$ (at $t=0$ every realization comes from time $0$).
--
--   Differences from the source:
--   - generalization: the adaptive process of §1.2 with static realizations 𝒮ᵗ → any probability space, any random static vectors S t and any random adversarial sample sets A ω t, with ℛᵗ the splice jointRealization S last; reason: same model as the published goal TemporalAgg.theorem_1_5; the paper process is the instance in which every sample taken at time s is a coordinate of one fresh vector 𝒮ˢ
--   - encoding: q adversarial samples; ATA performs samples → q = Σ_{t=1}^{T} |A t| and Σ_{t=1}^{T} ataAlg α A t; reason: counts up to the horizon T of the statement; the time-0 sampling is neither adversarial nor algorithmic
--   - encoding: probability at least 1 − ε·x → μ(bad event) ≤ x·ε in ℝ≥0∞, no measurability assumed; reason: outer measure of the complement event; same instances
--   - encoding: log_α T and log_α t, undefined at 0; "for any fixed time t" → Real.logb α 0 = 0 (factor 2 at T = 0 or t = 0), and the fixed-time clause for every t ≤ T; reason: at time 0 every realization comes from the single time step 0, so 2 is a valid factor; the hypothesis (and ℛᵗ's construction) only concerns times t ≤ T, the horizon of the statement
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §1.4, p.8, Theorem 1.6 (proved in §3.2, Lemmas 3.5 and 3.6, pp.18–19)

import Mathlib
import Definitions.Def_TemporalAgg_IsLoadFunction
import Definitions.Def_TemporalAgg_jointRealization
import Definitions.Def_TemporalAgg_Supplement_ataState

open MeasureTheory
open scoped ENNReal

namespace TemporalAgg.Supplement

/-- **Theorem 1.6** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against
Adaptive Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.8;
proved in §3.2, Lemmas 3.5 and 3.6, pp.18–19).

Let `f` be a load function on `𝒰ⁿ` and `α ≥ 2` an integer. Suppose that at every time `t ≤ T` the
static realization satisfies `f(𝒮ᵗ) ≤ L` with probability at least `1 − ε`. Then under Aligned
Temporal Aggregation with parameter `α`:
1. with probability at least `1 − ε(T + 1)`, `f(ℛᵗ) ≤ L·(log_α T + 2)` at all `t ≤ T` simultaneously;
2. for any fixed `t ≤ T`, this bound holds with probability at least `1 − ε(log_α t + 2)`;
3. if the adversary performs `q = ∑_{t=1}^{T} |A_t|` samples, ATA performs at most
   `q·α(log_α T + 1)` samples.

**Formalization Note** The probabilistic model is that of the published `TemporalAgg.theorem_1_5`
(clause 3): any probability space, any random static vectors `S t`, any random adversarial sample
sets `A ω t`, with `ℛᵗ` the splice `jointRealization S last` where `last` is ATA's state for
`A ω`; the paper's adaptive process is the instance where every sample taken at time `s` is a
coordinate of one fresh `𝒮ˢ`. Bad events are measured by `μ` as an outer measure in `ℝ≥0∞`, no
measurability is assumed, and `L`, `ε` are unconstrained. Logarithms are real
(`Real.logb α`, with `Real.logb α 0 = 0`, so at `t = 0` the factor is `2`). The sample counts are
those of `ataAlg` (the algorithm's re-samples of adversarially sampled objects included; the
time-0 sampling not counted). -/
theorem theorem_1_6 {U : Type*} {n : ℕ} (f : (Fin n → U) → ℝ) (hf : IsLoadFunction f)
    (α : ℕ) (hα : 2 ≤ α)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (∀ (S : ℕ → Ω → Fin n → U) (A : Ω → ℕ → Finset (Fin n)) (L : ℝ) (ε : ℝ≥0∞) (T : ℕ),
      (∀ t ≤ T, μ {ω | L < f (S t ω)} ≤ ε) →
      μ {ω | ∃ t ≤ T, (Real.logb α T + 2) * L <
          f (jointRealization S (fun ω => ataLast α (A ω)) ω t)} ≤ ((T : ℝ≥0∞) + 1) * ε ∧
      ∀ t ≤ T, μ {ω | (Real.logb α T + 2) * L <
          f (jointRealization S (fun ω => ataLast α (A ω)) ω t)} ≤
        ENNReal.ofReal (Real.logb α t + 2) * ε) ∧
    (∀ (A : ℕ → Finset (Fin n)) (T : ℕ),
      (∑ t ∈ Finset.Icc 1 T, (ataAlg α A t : ℝ)) ≤
        (∑ t ∈ Finset.Icc 1 T, ((A t).card : ℝ)) * (α * (Real.logb α T + 1))) := by sorry

end TemporalAgg.Supplement
