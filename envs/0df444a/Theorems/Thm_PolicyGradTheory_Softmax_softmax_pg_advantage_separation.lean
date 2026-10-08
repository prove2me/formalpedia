-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_pg_advantage_separation
-- name    : PolicyGradTheory.Softmax.softmax_pg_advantage_separation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:50:52.61899+00:00
-- url     : https://prove2.me/theorems/6b6934cd-db6b-4026-b749-3497c83a9e9d
-- title:
--   Lemma C.4, p. 62 — eventually A^{(t)}(s,a) < −Δ/4 on I^s_− and A^{(t)}(s,a) > Δ/4 on I^s_+ (41)
-- statement:
--   In the setting of Lemma C.2, let $V^{(\infty)}$ and $Q^{(\infty)}$ be the limits of $V^{(t)}$ and $Q^{(t)}$ (Lemma C.3), and define for each state $s$ the action sets
--   $$
--   I^s_0=\{a: Q^{(\infty)}(s,a)=V^{(\infty)}(s)\},\quad I^s_+=\{a: Q^{(\infty)}(s,a)>V^{(\infty)}(s)\},\quad I^s_-=\{a: Q^{(\infty)}(s,a)<V^{(\infty)}(s)\}.
--   $$
--   Let $\Delta>0$ satisfy $\Delta\le|Q^{(\infty)}(s,a)-V^{(\infty)}(s)|$ for every pair $(s,a)$ with $a\notin I^s_0$. Then there exists $T_1$ such that for all $t>T_1$, all states $s$ and all actions $a$,
--   $$
--   A^{(t)}(s,a)<-\frac{\Delta}{4}\ \text{ for } a\in I^s_-,\qquad A^{(t)}(s,a)>\frac{\Delta}{4}\ \text{ for } a\in I^s_+ . \tag{41}
--   $$
--
--   Eventually the sign of each advantage is frozen to the sign of its limit, which fixes the direction in which each parameter $\theta_{s,a}$ with $a\notin I^s_0$ moves.
--
--   **Formalization Note** The limits are parameters with the hypotheses that they are the limits of $V^{(t)}$ and $Q^{(t)}$. The paper's $\Delta=\min_{A^{(\infty)}(s,a)\ne0}|A^{(\infty)}(s,a)|$ is the largest admissible $\Delta$ when that set is nonempty; any smaller positive $\Delta$ is also allowed, and the statement is meaningful when the set is empty.
-- source:
--   arXiv:1908.00261v5, Lemma C.4, p. 62 (sets I^s_0, I^s_±, p. 62; Δ of Lemma C.3, p. 61)

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma C.4 (arXiv:1908.00261v5, p. 62): with `V^{(∞)}, Q^{(∞)}` the limits of Lemma C.3 and
`Δ > 0` a lower bound on every nonzero `|A^{(∞)}(s,a)| = |Q^{(∞)}(s,a) − V^{(∞)}(s)|`, there is
`T₁` such that for all `t > T₁`: `A^{(t)}(s,a) < −Δ/4` for `a ∈ I^s_−` and
`A^{(t)}(s,a) > Δ/4` for `a ∈ I^s_+` (41). -/
theorem softmax_pg_advantage_separation {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hηle : η ≤ (1 - γ) ^ 2 / 5)
    (Vinf : S → ℝ) (Qinf : S → A → ℝ)
    (hV : ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 (Vinf s)))
    (hQ : ∀ s a, Tendsto (fun t => QFunction (softmaxPolicy (θ t)) P r γ s a) atTop (𝓝 (Qinf s a)))
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔle : ∀ s a, Qinf s a ≠ Vinf s → Δ ≤ |Qinf s a - Vinf s|) :
    ∃ T1 : ℕ, ∀ t, T1 < t → ∀ s a,
      (Qinf s a < Vinf s → PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a < -(Δ / 4)) ∧
      (Vinf s < Qinf s a → Δ / 4 < PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a) := by sorry

end PolicyGradTheory.Softmax
