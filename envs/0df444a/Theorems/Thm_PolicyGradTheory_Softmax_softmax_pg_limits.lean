-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_pg_limits
-- name    : PolicyGradTheory.Softmax.softmax_pg_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:50:24.672228+00:00
-- url     : https://prove2.me/theorems/b3eb3656-6ee1-4449-bb75-1affe540a3ab
-- title:
--   Lemma C.3, p. 61 — the limits V^{(∞)}(s), Q^{(∞)}(s,a) exist and eventually Q^{(t)}(s,a) ≥ Q^{(∞)}(s,a) − Δ/4 (40)
-- statement:
--   In the setting of Lemma C.2 (finite MDP, $\mu\in\Delta(\mathcal S)$, softmax policy gradient ascent with $0<\eta\le(1-\gamma)^2/5$ from an arbitrary $\theta^{(0)}$), there exist values $V^{(\infty)}(s)$ and $Q^{(\infty)}(s,a)$ such that, as $t\to\infty$,
--   $$
--   V^{(t)}(s)\to V^{(\infty)}(s)\quad\text{and}\quad Q^{(t)}(s,a)\to Q^{(\infty)}(s,a)\qquad\text{for all } s,a .
--   $$
--   Moreover, for every $\Delta>0$ there is $T_0$ such that for all $t>T_0$, all states $s$ and all actions $a$,
--   $$
--   Q^{(t)}(s,a)\ge Q^{(\infty)}(s,a)-\Delta/4. \tag{40}
--   $$
--
--   In the paper $\Delta=\min\{|A^{(\infty)}(s,a)| : A^{(\infty)}(s,a)\ne0\}$ with $A^{(\infty)}=Q^{(\infty)}-V^{(\infty)}$; the statement here holds for every positive $\Delta$, which covers that choice whenever the index set is nonempty.
--
--   **Formalization Note** The paper's minimum is undefined when every $A^{(\infty)}(s,a)$ is zero; quantifying over every $\Delta>0$ avoids assigning it a value.
-- source:
--   arXiv:1908.00261v5, Lemma C.3, p. 61

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma C.3 (arXiv:1908.00261v5, p. 61): under the hypotheses of Lemma C.2 the limits
`V^{(∞)}(s)` and `Q^{(∞)}(s,a)` exist, and for every `Δ > 0` there is `T₀` with
`Q^{(t)}(s,a) ≥ Q^{(∞)}(s,a) − Δ/4` for all `t > T₀`, `s`, `a` (40). -/
theorem softmax_pg_limits {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hηle : η ≤ (1 - γ) ^ 2 / 5) :
    ∃ (Vinf : S → ℝ) (Qinf : S → A → ℝ),
      (∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 (Vinf s))) ∧
      (∀ s a, Tendsto (fun t => QFunction (softmaxPolicy (θ t)) P r γ s a) atTop
        (𝓝 (Qinf s a))) ∧
      ∀ Δ : ℝ, 0 < Δ → ∃ T0 : ℕ, ∀ t, T0 < t → ∀ s a,
        Qinf s a - Δ / 4 ≤ QFunction (softmaxPolicy (θ t)) P r γ s a := by sorry

end PolicyGradTheory.Softmax
