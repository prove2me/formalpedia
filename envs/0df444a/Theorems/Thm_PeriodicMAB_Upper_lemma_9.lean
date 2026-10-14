-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_9
-- name    : PeriodicMAB.Upper.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:56.768254+00:00
-- url     : https://prove2.me/theorems/e02b854a-be72-407d-959b-92b674709a29
-- title:
--   Lemma 9, p. 22 — for the oracle, $P(\mathcal E)\ge1-\delta S$
-- statement:
--   Let the noise satisfy Assumption 2 with parameter $\sigma>0$, let every arm have a mean sequence of minimum period $T_k$, assume Assumption 3 and $nK\le T$, and let $\delta\in(0,1)$. For the weak oracle (Algorithm 2 run with the true periods), the event
--   $$
--   \mathcal E=\Big\{\big|\tilde m^{(s)}_{k,t}-\mu_{k,t}\big|\le\tilde w^{(s)}_{k,t}\ \ \forall k\in\mathcal K,\ t\in\{nK+1,\dots,T\},\ s\in\mathcal S\Big\}
--   $$
--   satisfies $\mathbb P(\mathcal E)\ge1-\delta S$, where $\mathcal S=\{1,\dots,S\}$ and $S=\lfloor\log_2T\rfloor$.
--
--   On $\mathcal E$ every estimated mean of the oracle's tournament is within its confidence width of the true mean, which is what the screening analysis of Lemma 10 needs.
--
--   **Formalization Note** Stated as $\mathbb P(\mathcal E^c)\le\delta S$ (outer measure). Assumption 3 and $nK\le T$ are standing assumptions of §4 (stage two exists and every phase is sampled in stage one); they are recorded as hypotheses. The oracle uses arbitrary exploration length $n$ here, not necessarily (7).
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 22, Lemma 9

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 9 (p. 22): for the oracle policy with any `δ ∈ (0,1)`, the event `ℰ` that
`|m̃^(s)_{k,t} − µ_{k,t}| ≤ w̃^(s)_{k,t}` for all arms, all stage-two epochs `t ≤ T` and all
rounds `s ∈ 𝒮` has `P(ℰ) ≥ 1 − δS`, `S = ⌊log₂ T⌋`. -/
theorem lemma_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n g : ℕ) (δ : ℝ)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (hA3 : Assumption3 T n g Tper) (hnK : n * K ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    P (eventE μ ε σ δ T n Tper)ᶜ ≤ ENNReal.ofReal (δ * Nat.log 2 T) := by sorry

end PeriodicMAB.Upper
