-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_lemma_8
-- name    : SeqSocialLearning.Adequate.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:07.970395+00:00
-- url     : https://prove2.me/theorems/3444764d-d90d-4d92-8054-eb306634a03a
-- title:
--   Lemma 8, p. 18 — if learning fails, a positive-measure B where failure persists and near-B beliefs act almost optimally on B
-- statement:
--   Let $u \in U$ and let $M$ bound all payoffs, $|u(a,\omega)| \le M$. Let $\sigma$ be a perfect Bayesian equilibrium such that, for some $r' > 0$,
--   $$
--   P_\sigma\big(O(\omega) - u(a_t,\omega) > r' \text{ infinitely often}\big) > r'. \tag{12}
--   $$
--   Then there exists a measurable event $B \subseteq \Omega$ such that:
--
--   1. $\mu(B) > 0$;
--   2. for some $r > 0$, with $P^B_\sigma$ the play measure conditioned on the true state lying in $B$,
--   $$
--   P^B_\sigma\Big(\inf_{\omega'\in B}\big[O(\omega') - u(a_t,\omega')\big] > r \text{ infinitely often}\Big) > r ;
--   $$
--   3. there exists $\delta > 0$ such that, whenever $\nu \in \Delta(\Omega)$ satisfies $\nu(B) \ge 1-\delta$, every best reply $a^*$ to $\nu$ satisfies, for every $\omega \in B$,
--   $$
--   |O(\omega) - u(a^*,\omega)| \le \frac{r(1-2\delta) - 4\delta M}{2(1-\delta)} .
--   $$
--
--   The proof of Theorem 1 uses $B$ to build a limit belief at which a private signal has positive value, contradicting Lemma 2.
--
--   **Formalization Note** The paper writes $\min_{\omega'\in B}$; the minimum need not be attained, so it is the infimum. This is at least as strong as "for every $\omega' \in B$". The $r$ of item 3 is the same $r$ as in item 2. A best reply to $\nu$ is an action $a^*$ with $E_\nu[u(b,\omega)] \le E_\nu[u(a^*,\omega)]$ for all $b$.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 18, Lemma 8 (equation (12))

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals

open MeasureTheory ProbabilityTheory Filter Topology

namespace SeqSocialLearning.Adequate

/-- **Lemma 8** (p. 18). Let `M` bound all payoffs of `u`. If `σ` is a perfect Bayesian
equilibrium such that (12) holds for some `r' > 0`, i.e.
`Pσ(O(ω) − u(a_t, ω) > r' infinitely often) > r'`, then there is a measurable event `B ⊆ Ω` with
1. `µ(B) > 0`,
2. `P^B_σ(inf_{ω' ∈ B} [O(ω') − u(a_t, ω')] > r infinitely often) > r` for some `r > 0`,
3. there is `δ > 0` such that if `ν ∈ ∆(Ω)` satisfies `ν(B) ≥ 1 − δ`, then for every `ω ∈ B`,
   `|O(ω) − u(a*, ω)| ≤ (r(1 − 2δ) − 4δM) / (2(1 − δ))` for every best reply `a*` to `ν`. -/
theorem lemma_8 {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F)
    (u : A → Ω → ℝ) (hu : InU u) (M : ℝ) (hM : ∀ a ω, |u a ω| ≤ M)
    (p : Profile A S) (hp : IsPBE μ F u p) (r' : ℝ) (hr' : 0 < r')
    (h12 : ENNReal.ofReal r' < playMeasure μ F p
      {x | ∃ᶠ t in atTop, r' < maxPayoff u (state x) - u (action x t) (state x)}) :
    ∃ B : Set Ω, MeasurableSet B ∧ 0 < μ B ∧
      ∃ r : ℝ, 0 < r ∧
        ENNReal.ofReal r < (playMeasure μ F p)[|state ⁻¹' B]
          {x | ∃ᶠ t in atTop, r < ⨅ ω' : B, (maxPayoff u ω' - u (action x t) ω')} ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ ν : Measure Ω, IsProbabilityMeasure ν → 1 - δ ≤ ν.real B →
            ∀ aStar : A, (∀ b : A, ∫ ω, u b ω ∂ν ≤ ∫ ω, u aStar ω ∂ν) →
              ∀ ω ∈ B, |maxPayoff u ω - u aStar ω| ≤
                (r * (1 - 2 * δ) - 4 * δ * M) / (2 * (1 - δ)) := by sorry

end SeqSocialLearning.Adequate
