-- Prove2me | Theorems.Thm_SampleComplexityRL_CPI_example_tight
-- name    : SampleComplexityRL.CPI.example_tight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:17.629196+00:00
-- url     : https://prove2.me/theorems/88d570be-0d3b-4c90-87c2-b1c93dcc212d
-- title:
--   Example 7.4.1 — the improvement bound of Lemma 7.2.2 is tight for all α and γ
-- statement:
--   Consider the two-state MDP with states $i,j$ and actions $1,2$ at each state. At $i$, action $1$ is a self transition with reward $r(i,1)=\tfrac12$ and action $2$ moves to $j$ with reward $r(i,2)=1$. At $j$ both actions are self transitions, with $r(j,1)=\tfrac12$ and $r(j,2)=0$. The reset distribution is the point mass at $i$. Let $\pi$ be the deterministic policy $\pi(i)=\pi(j)=1$, $\pi'$ the deterministic policy $\pi'(i)=\pi'(j)=2$, and $\pi_{\rm new}=(1-\alpha)\pi+\alpha\pi'$. Values are normalized and $0\le\gamma<1$, $0\le\alpha\le1$.
--
--   Then:
--   1. $d_{\pi,i}(i)=1$;
--   2. $A_\pi(i,2)=(1-\gamma)/2$, $A_\pi(j,2)=-(1-\gamma)/2$, and $A_\pi(i,1)=A_\pi(j,1)=0$;
--   3. the future advantage is $\mathbb A_\pi(i,\pi')=(1-\gamma)/2$ and $\epsilon_\infty=\max_s|\mathbb E_{a\sim\pi'(\cdot\mid s)}A_\pi(s,a)|=(1-\gamma)/2$;
--   4. $V_\pi(i)=\tfrac12$ and
--   $$V_{\pi_{\rm new}}(i)=\frac12+\frac\alpha2-\frac{\gamma\alpha^2}{1-\gamma(1-\alpha)};$$
--   5. consequently the improvement equals the lower bound of Lemma 7.2.2:
--   $$V_{\pi_{\rm new}}(i)-V_\pi(i)=\frac{\alpha}{1-\gamma}\Big(\mathbb A_\pi(i,\pi')-\frac{2\gamma\alpha}{1-\gamma(1-\alpha)}\epsilon_\infty\Big).$$
--
--   The example shows that the conservative-update bound cannot be improved uniformly in $\alpha$ and $\gamma$, which is why CPI's step size is set from the worst case.
--
--   **Formalization Note** The thesis writes the state $i$ as "1" in its last two displays; here it is $i$. The actions $1,2$ are the constructors `one`, `two`, and $\pi,\pi'$ are indicator policies.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 94, Example 7.4.1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_CPI_ExactCPI
open ApproxOptRL.Shared ApproxOptRL.CPI FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.CPI

/-- **Example 7.4.1** (Kakade 2003, p. 94): the improvement bound of Lemma 7.2.2 is tight for
all `α ∈ [0, 1]` and `γ ∈ [0, 1)`. Two states `i, j`, two actions `1, 2` (`one`, `two`),
reset distribution the point mass at `i`, `π` = always action `1`, `π'` = always action `2`,
`π_new = (1 − α)π + απ'`. Then `d_{π,i}(i) = 1`, `A_π(i,2) = (1−γ)/2`, `A_π(j,2) = −(1−γ)/2`,
the advantages of the actions taken by `π` are `0`, `𝔸_π(i, π') = (1−γ)/2`,
`ε_∞ = (1−γ)/2`, `V_π(i) = 1/2`, `V_{π_new}(i) = 1/2 + α/2 − γα²/(1 − γ(1 − α))`, and
`V_{π_new}(i) − V_π(i)` equals the right-hand side of Lemma 7.2.2. -/
theorem example_tight (γ α : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    let μ : ExState → ℝ := pointMass ExState.i
    let πnew : ExState → ExAction → ℝ := mixPolicy α exPi exPi'
    let εinf : ℝ := Finset.univ.sup' Finset.univ_nonempty
      (fun s => |∑ a, exPi' s a * advantage exP exR γ exPi s a|)
    futureStateDist exP γ exPi μ ExState.i = 1 ∧
    advantage exP exR γ exPi ExState.i ExAction.two = (1 - γ) / 2 ∧
    advantage exP exR γ exPi ExState.j ExAction.two = -((1 - γ) / 2) ∧
    advantage exP exR γ exPi ExState.i ExAction.one = 0 ∧
    advantage exP exR γ exPi ExState.j ExAction.one = 0 ∧
    policyAdvantage exP exR γ exPi μ exPi' = (1 - γ) / 2 ∧
    εinf = (1 - γ) / 2 ∧
    value exP exR γ exPi ExState.i = 1 / 2 ∧
    value exP exR γ πnew ExState.i = 1 / 2 + α / 2 - γ * α ^ 2 / (1 - γ * (1 - α)) ∧
    value exP exR γ πnew ExState.i - value exP exR γ exPi ExState.i =
      α / (1 - γ) * (policyAdvantage exP exR γ exPi μ exPi' -
        2 * γ * α / (1 - γ * (1 - α)) * εinf) := by sorry

end SampleComplexityRL.CPI
