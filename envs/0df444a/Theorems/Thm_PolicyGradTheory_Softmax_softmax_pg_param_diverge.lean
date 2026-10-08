-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_pg_param_diverge
-- name    : PolicyGradTheory.Softmax.softmax_pg_param_diverge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:51:29.797025+00:00
-- url     : https://prove2.me/theorems/d91ca29c-9813-4b48-a0cf-15c7c3332f54
-- title:
--   Lemma C.7, pp. 63–64 — if I^s_+ ≠ ∅ then max_{a∈I^s_0} θ^{(t)}_{s,a} → ∞ and min_{a∈A} θ^{(t)}_{s,a} → −∞
-- statement:
--   In the setting of Lemma C.5, let $s$ be a state with $I^s_+\ne\emptyset$, i.e. some action $a$ has $Q^{(\infty)}(s,a)>V^{(\infty)}(s)$. Then
--   $$
--   \max_{a\in I^s_0}\theta^{(t)}_{s,a}\to\infty,\qquad\min_{a\in\mathcal A}\theta^{(t)}_{s,a}\to-\infty\qquad(t\to\infty).
--   $$
--
--   The first limit is stated as: for every $M\in\mathbb R$ there is $T$ such that for all $t\ge T$ some $a\in I^s_0$ has $\theta^{(t)}_{s,a}\ge M$ (this also says $I^s_0\neq\emptyset$).
--
--   This lemma is a step of the paper's proof by contradiction of Theorem 5.1, which shows $I^s_+=\emptyset$ for every state; its hypothesis is therefore never met by an actual run, and the lemma is a building block of that argument rather than a description of a run's behaviour.
--
--   **Formalization Note** "$\to-\infty$" is `Tendsto … atTop atBot`; the minimum over $\mathcal A$ is `Finset.inf'` over the nonempty finite action set.
-- source:
--   arXiv:1908.00261v5, Lemma C.7, p. 63 (proof pp. 63–64)

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma C.7 (arXiv:1908.00261v5, pp. 63–64): for every state `s` with `I^s_+ ≠ ∅`,
`max_{a ∈ I^s_0} θ^{(t)}_{s,a} → ∞` and `min_{a ∈ A} θ^{(t)}_{s,a} → −∞`. The first limit is written
as: for every `M`, eventually some `a ∈ I^s_0` has `θ^{(t)}_{s,a} ≥ M`. -/
theorem softmax_pg_param_diverge {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hμpos : ∀ s, 0 < μ s) (hηle : η ≤ (1 - γ) ^ 3 / 8)
    (Vinf : S → ℝ) (Qinf : S → A → ℝ)
    (hV : ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 (Vinf s)))
    (hQ : ∀ s a, Tendsto (fun t => QFunction (softmaxPolicy (θ t)) P r γ s a) atTop (𝓝 (Qinf s a)))
    (s : S) (hplus : ∃ a, Vinf s < Qinf s a) :
    (∀ M : ℝ, ∃ T : ℕ, ∀ t, T ≤ t → ∃ a, Qinf s a = Vinf s ∧ M ≤ θ t (s, a)) ∧
    Tendsto (fun t => Finset.univ.inf' Finset.univ_nonempty (fun a => θ t (s, a))) atTop atBot := by sorry

end PolicyGradTheory.Softmax
