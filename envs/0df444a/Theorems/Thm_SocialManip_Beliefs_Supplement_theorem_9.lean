-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_theorem_9
-- name    : SocialManip.Beliefs.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:22:03.544869+00:00
-- url     : https://prove2.me/theorems/9e821057-e12b-46c1-a403-2bf8c5bff574
-- title:
--   Theorem 9, p. 36 (corrected: generic parameters) — impervious iff 0 ∈ Γ*; a knife-edge two-agent network shows the exclusion is needed
-- statement:
--   Let $\Gamma^*$ be the set of maximizers of the principal's binary program on p. 36,
--   $$\max_{\gamma,r\in\{0,1\}^n}\ \sum_{i\in D}(r_i-\varepsilon\gamma_i)\quad\text{s.t.}\quad r_i\le D_i(\gamma)+\tfrac{1+b}{2}\ \ \forall i,$$
--   where $D_i(\gamma)$ is the DeGroot centrality (Definition 4) and $\gamma$ vanishes on Bayesians. Fix the network, the Bayesian set, the signal qualities $p_i\in[1/2,1)$, a prior $q\in(0,1)$ and $\lambda^*>0$. There is a Lebesgue-null set $\mathcal P\subset\mathbb R^2_+\times(-1,1)$ such that for every $(\varepsilon,\lambda,b)\notin\mathcal P$ satisfying Assumption 1,
--   $$\text{the network is impervious}\iff 0\in\Gamma^*,$$
--   that is, it is impervious if $0\in\Gamma^*$ and susceptible otherwise. Without the genericity exclusion the characterization fails. In the two-agent network with Bayesian $0$ and a DeGroot $1$ with weights $\theta_1=\alpha_{10}=1/2$, $p_i=3/4$, $q=1/2$, $\lambda=\lambda^*=1$, $\varepsilon=1/2$, $b=0$, all assumptions hold, and
--   $$\text{the network is impervious},\qquad (\gamma=0,r=0)\notin\Gamma^*.$$
--   Theorem 9 reduces the equilibrium extent of manipulation to a finite integer program over influence vectors.
--
--   **Formalization Note** The proof (p. 57) rests on equilibrium play being pinned down by limiting beliefs, which is the generic situation of Theorem 1. The exceptional set is the same kind of object as Theorem 1's: it excludes a limiting centrality exactly on the threshold $(1-b)/2$ (finitely many $b$) and payoff ties $\sum_i r_i=\varepsilon\sum_i\gamma_i$ (rational $\varepsilon$). The two-agent example is such a knife edge: $D_1=1/2=(1-b)/2$, so the non-strict program admits $\gamma_1=r_1=1$ with objective $1/2$. Yet the DeGroot's belief of $R$ is $\tfrac12\mathrm{BU}_1(R)<\tfrac12$ in state $S$ and $\tfrac12+\tfrac12\mathrm{BU}_1(R)>\tfrac12$ in state $R$ at every positive finite horizon, so she always acts correctly. DISPROOF.md retains the calculation.
--
--   Differences from the source:
--   - correction: impervious iff 0 ∈ Γ*, for every parameter → the same characterization outside a Lebesgue-null set of (ε, λ, b), together with an explicit knife-edge counterexample showing that the exclusion is necessary; reason: the non-strict program counts a limiting belief equal to the threshold as manipulable, while every finite-time belief can stay strictly on the correct side; the proof relies on the pinned-down play of Theorem 1, which is generic
--   - reading: Theorem 9 is printed without its standing assumptions → Assumption 1, q ∈ (0,1), λ* > 0 at the varied parameters; reason: the proof on p. 57 uses Theorem 8 and Proposition 2, which rest on them
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Theorem 9 and the principal's program, p. 36; proof p. 57

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open MeasureTheory

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- Theorem 9 under the genericity of Theorem 1, and its printed boundary refuted.
(1) Outside a Lebesgue-null set of `(ε, λ, b)`, a network satisfying Assumption 1 is impervious
if and only if the zero vector belongs to the argmax `Γ*` of the principal's integer program
(p. 36); the proof on p. 57 rests on the pinned-down equilibrium play of Theorem 1.
(2) Without genericity the characterization fails. The Bayesian is agent 0; agent 1 gives
weight 1/2 to personal experience and 1/2 to the Bayesian. Every finite-time personal posterior
is strictly between 0 and 1, so the DeGroot always takes the correct action after the first
update. Nevertheless, the printed IP admits r₁ = γ₁ = 1 with profit 1/2. -/
theorem theorem_9 :
    (∀ {n : ℕ} (M : Model n), M.Standing → (0 < M.q ∧ M.q < 1) → 0 < M.lamStar →
      ∀ adj : Fin n → Fin n → Prop,
      ∃ Pset : Set (ℝ × ℝ × ℝ), Pset ⊆ Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.Ioo (-1) 1 ∧
        volume Pset = 0 ∧
        ∀ e l c : ℝ, 0 < e → 0 < l → -1 < c → c < 1 → (e, l, c) ∉ Pset →
          ({ M with ε := e, lam := l, b := c } : Model n).Assumption1 adj →
          (Impervious ({ M with ε := e, lam := l, b := c } : Model n) ↔
            ((fun _ => false, fun _ => false) ∈
              ipArgmax ({ M with ε := e, lam := l, b := c } : Model n)))) ∧
    (let M : Model 2 :=
      { B := {0}
        θ := fun _ => 1 / 2
        α := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 / 2 else 0
        p := fun _ => 3 / 4
        q := 1 / 2
        lam := 1
        lamStar := 1
        ε := 1 / 2
        b := 0 }
    M.Standing ∧ M.GameDomain ∧ M.Assumption1 (fun i j => i ≠ j) ∧
      Impervious M ∧ ((fun _ => false, fun _ => false) ∉ ipArgmax M)) := by sorry

end SocialManip.Beliefs.Supplement
