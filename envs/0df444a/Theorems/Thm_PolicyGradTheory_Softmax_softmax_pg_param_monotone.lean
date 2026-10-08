-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_pg_param_monotone
-- name    : PolicyGradTheory.Softmax.softmax_pg_param_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:51:20.512962+00:00
-- url     : https://prove2.me/theorems/231e399d-1d31-4901-850c-4ad852719f71
-- title:
--   Lemma C.6, p. 63 — eventually θ^{(t)}_{s,a} strictly increases for a ∈ I^s_+ and strictly decreases for a ∈ I^s_−
-- statement:
--   In the setting of Lemma C.5 (finite MDP, strictly positive $\mu$, softmax policy gradient ascent with $0<\eta\le(1-\gamma)^3/8$, limits $V^{(\infty)}$, $Q^{(\infty)}$ and sets $I^s_\pm$), there exists $T_1$ such that for every state $s$:
--
--   1. for every $a\in I^s_+$, the sequence $t\mapsto\theta^{(t)}_{s,a}$ is strictly increasing on $t\ge T_1$;
--   2. for every $a\in I^s_-$, the sequence $t\mapsto\theta^{(t)}_{s,a}$ is strictly decreasing on $t\ge T_1$.
--
--   In the paper $T_1$ is the time of Lemma C.4; the statement asserts the existence of such a time.
--
--   **Formalization Note** "Strictly increasing for $t\ge T_1$" is `StrictMonoOn` on $\{t\in\mathbb N: t\ge T_1\}$.
-- source:
--   arXiv:1908.00261v5, Lemma C.6, p. 63

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma C.6 (arXiv:1908.00261v5, p. 63): there is `T₁` such that, for `t ≥ T₁`, the parameter
`θ^{(t)}_{s,a}` is strictly increasing for `a ∈ I^s_+` and strictly decreasing for `a ∈ I^s_−`. -/
theorem softmax_pg_param_monotone {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hμpos : ∀ s, 0 < μ s) (hηle : η ≤ (1 - γ) ^ 3 / 8)
    (Vinf : S → ℝ) (Qinf : S → A → ℝ)
    (hV : ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 (Vinf s)))
    (hQ : ∀ s a, Tendsto (fun t => QFunction (softmaxPolicy (θ t)) P r γ s a) atTop (𝓝 (Qinf s a))) :
    ∃ T1 : ℕ, ∀ s a,
      (Vinf s < Qinf s a → StrictMonoOn (fun t => θ t (s, a)) (Set.Ici T1)) ∧
      (Qinf s a < Vinf s → StrictAntiOn (fun t => θ t (s, a)) (Set.Ici T1)) := by sorry

end PolicyGradTheory.Softmax
