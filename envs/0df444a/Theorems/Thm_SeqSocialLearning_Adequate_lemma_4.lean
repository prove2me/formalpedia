-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_lemma_4
-- name    : SeqSocialLearning.Adequate.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:04.22738+00:00
-- url     : https://prove2.me/theorems/a6772418-3682-4bff-a84d-86b05d2971db
-- title:
--   Lemma 4, p. 13 — an ε-optimal strategy that is constant on a finite product partition with finitely many actions
-- statement:
--   Let $T$ and $S$ be standard Borel signal spaces, $\lambda \in \Delta(\Omega\times T\times S)$, and $u \in U$. An agent observes $(t, s)$, drawn with $\lambda$, and then takes an action $a \in A$. Let $m$ be the maximal expected utility the agent can achieve:
--   $$
--   m = \sup_{\tau} E_\lambda[u(\tau(t,s),\omega)],
--   $$
--   the supremum over measurable strategies $\tau : T\times S \to A$.
--
--   For every $\varepsilon > 0$ there exist a finite measurable product partition $K$ of $T\times S$, a finite set of actions $A_f$, and a strategy $\tau : T\times S \to A_f$, measurable with respect to $K$, that guarantees expected utility at least $m - \varepsilon$.
--
--   In the proof of Lemma 2 this discretization turns the limit decision problem into strategies that finitely many agents can imitate.
--
--   **Formalization Note** The product partition is $\{\, i^{-1}(k) \times j^{-1}(l) \,\}$ for measurable maps $i : T \to \{1,\dots,n_1\}$ and $j : S \to \{1,\dots,n_2\}$; any finite partition of $T\times S$ into measurable rectangles refines to such a grid. The strategy is $\tau(t,s) = g(i(t), j(s))$, and $A_f$ is the range of $g$.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 12 (single agent decision problem), p. 13, Lemma 4

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Beliefs

open MeasureTheory ProbabilityTheory Filter Topology

namespace SeqSocialLearning.Adequate

/-- **Lemma 4** (p. 13). In the single-agent decision problem of p. 12 (signals `(t, s)` drawn
with `λ ∈ ∆(Ω × T × S)`, utility `u ∈ U`, value `m`), for every `ε > 0` there are a finite
measurable product partition `K = {i⁻¹(k) × j⁻¹(l)}` of `T × S`, a finite set of actions
`A_f = range g` and a strategy `τ(t, s) = g(i t, j s)`, measurable with respect to `K`, with
expected utility at least `m − ε`. -/
theorem lemma_4 {Ω A S T : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace T] [StandardBorelSpace T]
    (lam : Measure (Ω × T × S)) [IsProbabilityMeasure lam]
    (u : A → Ω → ℝ) (hu : InU u) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n₁ n₂ : ℕ) (i : T → Fin n₁) (j : S → Fin n₂) (g : Fin n₁ → Fin n₂ → A),
      Measurable i ∧ Measurable j ∧
        decisionValue lam u - ε ≤ ∫ z, u (g (i z.2.1) (j z.2.2)) z.1 ∂lam := by sorry

end SeqSocialLearning.Adequate
