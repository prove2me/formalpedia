-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_pg_gradient_vanishes
-- name    : PolicyGradTheory.Softmax.softmax_pg_gradient_vanishes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:50:45.736352+00:00
-- url     : https://prove2.me/theorems/b3968f3f-e043-4113-bc35-318e4e9265e9
-- title:
--   Lemma C.5, pp. 62–63 — ∂V^{(t)}(µ)/∂θ_{s,a} → 0, π^{(t)}(a|s) → 0 on I^s_+ ∪ I^s_−, and Σ_{a∈I^s_0} π^{(t)}(a|s) → 1
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$, $\mathcal A$ nonempty, and $\mu$ a **strictly positive** distribution on $\mathcal S$. Let $(\theta^{(t)})$ be a run of softmax policy gradient ascent $\theta^{(t+1)}=\theta^{(t)}+\eta\nabla_\theta V^{(t)}(\mu)$ with $0<\eta\le(1-\gamma)^3/8$, and let $V^{(\infty)}$, $Q^{(\infty)}$ be the limits of $V^{(t)}$, $Q^{(t)}$, with $I^s_0, I^s_\pm$ as in Lemma C.4. Then:
--
--   1. $\displaystyle\frac{\partial V^{(t)}(\mu)}{\partial\theta_{s,a}}\to0$ as $t\to\infty$, for all states $s$ and actions $a$;
--   2. $\pi^{(t)}(a\mid s)\to0$ for every $a\in I^s_+\cup I^s_-$;
--   3. $\displaystyle\sum_{a\in I^s_0}\pi^{(t)}(a\mid s)\to1$ for every state $s$.
--
--   Here $\pi^{(t)}=\pi_{\theta^{(t)}}$. The lemma is where strict positivity of $\mu$ enters: it keeps the visitation weight $d^{(t)}_\mu(s)$ bounded away from zero.
--
--   **Formalization Note** $\partial/\partial\theta_{s,a}$ is the $(s,a)$ coordinate of Mathlib's `gradient`. The added hypothesis $\eta>0$ is implicit in "gradient ascent".
-- source:
--   arXiv:1908.00261v5, Lemma C.5, p. 62 (proof p. 63), under the assumptions of Theorem 5.1, p. 18

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma C.5 (arXiv:1908.00261v5, pp. 62–63): for strictly positive `µ` and `η ≤ (1−γ)³/8`,
`∂V^{(t)}(µ)/∂θ_{s,a} → 0` for all `s, a`; hence `π^{(t)}(a|s) → 0` for `a ∈ I^s_+ ∪ I^s_−` and
`∑_{a ∈ I^s_0} π^{(t)}(a|s) → 1`. -/
theorem softmax_pg_gradient_vanishes {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hμpos : ∀ s, 0 < μ s) (hηle : η ≤ (1 - γ) ^ 3 / 8)
    (Vinf : S → ℝ) (Qinf : S → A → ℝ)
    (hV : ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 (Vinf s)))
    (hQ : ∀ s a, Tendsto (fun t => QFunction (softmaxPolicy (θ t)) P r γ s a) atTop (𝓝 (Qinf s a))) :
    (∀ s a, Tendsto (fun t => gradient (softmaxValue P r γ μ) (θ t) (s, a)) atTop (𝓝 0)) ∧
    (∀ s a, Qinf s a ≠ Vinf s → Tendsto (fun t => softmaxPolicy (θ t) s a) atTop (𝓝 0)) ∧
    (∀ s, Tendsto (fun t => ∑ a ∈ Finset.univ.filter (fun a => Qinf s a = Vinf s),
      softmaxPolicy (θ t) s a) atTop (𝓝 1)) := by sorry

end PolicyGradTheory.Softmax
