-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_lemma2_dynamic_programming
-- name    : PosteriorSamplingRL.Regret.lemma2_dynamic_programming
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:16.752981+00:00
-- url     : https://prove2.me/theorems/a4abb989-3ded-4fcc-aa5e-122313e224a1
-- title:
--   Lemma 2, (5), p. 5 — dynamic programming equation V^M_{µ,i} = T^M_{µ(·,i)} V^M_{µ,i+1}, V^M_{µ,τ+1} = 0
-- statement:
--   Let $M_\theta$ be a finite MDP of the family, with reward distributions supported on $[0,1]$, and let $\mu:\mathcal S\times\{1,\dots,\tau\}\to\mathcal A$ be a deterministic policy. The path-defined value functions satisfy
--   $$
--   V^\theta_{\mu,i}=\mathcal T^\theta_{\mu(\cdot,i)}V^\theta_{\mu,i+1}\qquad(i=1,\dots,\tau),
--   $$
--   with $V^\theta_{\mu,\tau+1}=0$, where $\mathcal T^\theta_d V(s)=\overline R^\theta_{d(s)}(s)+\sum_{s'}P^\theta_{d(s)}(s'\mid s)V(s')$ is the Bellman operator of the stationary rule $d=\mu(\cdot,i)$.
--
--   The equation lets one compare value functions of two MDPs one step at a time; it is the tool behind the Bellman-error decomposition (6).
--
--   **Formalization Note** Steps are 0-based: the conclusion is stated for Lean steps $j<\tau$, the paper's $i=j+1$, and $V^\theta_{\mu,\tau+1}=0$ is `value F θ π τ = 0`. The value is defined by the expectation along the trajectory, not by this recursion, so the equation is not definitional.
-- source:
--   arXiv:1306.0940v5, Lemma 2, (5), p. 5

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_MDP

open MeasureTheory ProbabilityTheory

namespace PosteriorSamplingRL.Regret

/-- Lemma 2 (Dynamic programming equation), (5) (arXiv:1306.0940v5, p. 5). For every MDP `M_θ`
and policy `π : S × {1, …, τ} → A`, `V^θ_{π,i} = T^θ_{π(·,i)} V^θ_{π,i+1}` for `i = 1, …, τ`, with
`V^θ_{π,τ+1} = 0`. In 0-based steps: `value j = T_{π(·,j)} (value (j+1))` for `j < τ`, and
`value τ = 0`. -/
theorem lemma2_dynamic_programming (S A τ : ℕ) (Θ : Type) [MeasurableSpace Θ]
    (F : MDPFamily S A Θ) (θ : Θ) (π : Policy S A τ) :
    (∀ (j : ℕ) (hj : j < τ) (s : Fin S),
      value F θ π j s = bellman F θ (fun s' => π s' ⟨j, hj⟩) (value F θ π (j + 1)) s) ∧
    value F θ π τ = 0 := by sorry

end PosteriorSamplingRL.Regret
