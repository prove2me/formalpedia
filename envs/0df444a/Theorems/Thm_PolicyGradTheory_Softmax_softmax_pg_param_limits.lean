-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_pg_param_limits
-- name    : PolicyGradTheory.Softmax.softmax_pg_param_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:51:34.722979+00:00
-- url     : https://prove2.me/theorems/dd141e34-7906-400a-ae72-58f985ffe6f7
-- title:
--   Lemma C.11, pp. 65–66 — θ^{(t)}_{s,a} is bounded below for a ∈ I^s_+ and θ^{(t)}_{s,a} → −∞ for a ∈ I^s_−
-- statement:
--   In the setting of Lemma C.5 (finite MDP, strictly positive $\mu$, softmax policy gradient ascent with $0<\eta\le(1-\gamma)^3/8$, limits $V^{(\infty)}$, $Q^{(\infty)}$ and sets $I^s_\pm$), for every state $s$:
--
--   1. for every $a\in I^s_+$, the sequence $\theta^{(t)}_{s,a}$ is bounded from below;
--   2. for every $a\in I^s_-$, $\theta^{(t)}_{s,a}\to-\infty$ as $t\to\infty$.
--
--   Together with Lemma C.7 this pins down where the parameters of a run go, and it is the input to the final contradiction in the proof of Theorem 5.1.
--
--   **Formalization Note** The paper says "bounded from below as $t\to\infty$". Every $\theta^{(t)}$ is a finite vector, so eventual boundedness from below is the same as boundedness from below of the whole sequence, which is how it is stated.
-- source:
--   arXiv:1908.00261v5, Lemma C.11, p. 65 (proof pp. 65–66)

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma C.11 (arXiv:1908.00261v5, pp. 65–66): for `a ∈ I^s_+`, `θ^{(t)}_{s,a}` is bounded from
below; for `a ∈ I^s_−`, `θ^{(t)}_{s,a} → −∞`. -/
theorem softmax_pg_param_limits {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hμpos : ∀ s, 0 < μ s) (hηle : η ≤ (1 - γ) ^ 3 / 8)
    (Vinf : S → ℝ) (Qinf : S → A → ℝ)
    (hV : ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 (Vinf s)))
    (hQ : ∀ s a, Tendsto (fun t => QFunction (softmaxPolicy (θ t)) P r γ s a) atTop (𝓝 (Qinf s a))) :
    ∀ s a,
      (Vinf s < Qinf s a → BddBelow (Set.range (fun t => θ t (s, a)))) ∧
      (Qinf s a < Vinf s → Tendsto (fun t => θ t (s, a)) atTop atBot) := by sorry

end PolicyGradTheory.Softmax
