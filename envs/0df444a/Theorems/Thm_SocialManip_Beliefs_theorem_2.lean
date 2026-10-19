-- Prove2me | Theorems.Thm_SocialManip_Beliefs_theorem_2
-- name    : SocialManip.Beliefs.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:13.299967+00:00
-- url     : https://prove2.me/theorems/d043855d-4e0a-46c0-9b3e-eeebebf4b339
-- title:
--   Theorem 2, p. 11 — under Assumption 1, for any principal action x*, beliefs converge a.s. to (I − W)^{-1}(BU(h_∞(x*))(y′|y) ⊙ θ)
-- statement:
--   Consider $n$ agents learning a binary state $y\in\{S,R\}$ whose prior probability of $S$ is $q\in(0,1)$. A set $B$ of agents is Bayesian: they know the realized state $y$ and always hold the correct belief. The other agents are DeGroot agents: agent $i\notin B$ has weights $\theta_i\ge0$, $\alpha_{ij}\ge0$ with $\theta_i+\sum_j\alpha_{ij}=1$. Every agent has a signal quality $p_i\in[1/2,1)$; organic news arrives at intensity $\lambda>0$ and is correct with probability $p_i$ (display (1)). A principal with influence state $\hat y$ targets the agents with $x_i=1$, sending them the message $\hat y$ at intensity $\lambda^*>0$, so a targeted agent's signal is the principal's message with probability $\lambda^*/(\lambda+\lambda^*)$ and organic news otherwise.
--
--   Agent $i$'s signals $s_{i,1},s_{i,2},\dots$ are independent over time with this law. Its personal experience $\mathrm{BU}_i(y'\mid h_{i,t})$ is the face-value Bayesian posterior of $y'$ given $s_{i,1},\dots,s_{i,t}$, and the beliefs follow the DeGroot update
--   $$\pi_{i,t+1}(y'\mid y)=\theta_i\,\mathrm{BU}_i(y'\mid h_{i,t+1})+\sum_{j=1}^n\alpha_{ij}\,\pi_{j,t}(y'\mid y)\quad(i\notin B),$$
--   from any initial belief in $[0,1]$, while $\pi_{i,t}(y'\mid y)=\mathbf 1[y'=y]$ for $i\in B$. Let $\mathbf W$ be the influence matrix (zero Bayesian rows, $\alpha_{ij}$ in DeGroot rows) and $\boldsymbol\theta=(\mathbf 1_B,\theta_{m+1},\dots,\theta_n)$.
--
--   Assume Assumption 1:
--
--   1. (i) $p_i<(\lambda^*+\lambda)/(2\lambda)$ for all agents $i$;
--   2. (ii) the graph $G^*$, in which a DeGroot agent $i$ links to $j$ exactly when $\alpha_{ij}>0$, is strongly connected;
--   3. (iii) for every DeGroot agent, $\theta_i>0$ if and only if $p_i>1/2$;
--   4. (iv) some agent has $p_i>1/2$.
--
--   Then, for any principal action $\mathbf x^*$, there are constants $\mathrm{BU}_i(h_{i,\infty}(\mathbf x^*))(y'\mid y)$ such that almost surely each DeGroot agent's personal experience converges to its constant and the beliefs converge:
--   $$\boldsymbol\pi_t(y'\mid y)\xrightarrow{\text{a.s.}}(\mathbf I-\mathbf W)^{-1}\big(\mathrm{BU}(\mathbf h_\infty(\mathbf x^*))(y'\mid y)\odot\boldsymbol\theta\big),$$
--   where the Bayesian entries of $\mathrm{BU}(\mathbf h_\infty(\mathbf x^*))(y'\mid y)$ are the correct belief $\mathbf 1[y'=y]$.
--
--   This closed form is the paper's basis for deciding which agents the principal can manipulate: the terminal beliefs, and hence the agents' actions, are a linear function of the converged personal experiences through $(\mathbf I-\mathbf W)^{-1}$.
--
--   **Formalization Note** The realized state $y$, the influence state $\hat y$, the pure action $\mathbf x^*$ (§3.2 restricts to pure strategies without loss of generality) and the state $y'$ are fixed parameters. Only per-agent independence over time is assumed; signals of different agents may be dependent, as they are in the paper's model, where all targeted agents receive the same principal stream. Time is discrete and the history at $t$ is the signals at times $1,\dots,t$. The limit holds for every initial DeGroot belief in $[0,1]$ on the same almost-sure event, matching the page's belief simplex. The constants are deterministic and tied to $\mathrm{BU}_i$ by the first conclusion, so the limit is not an arbitrary vector. $G^*$ is given by a relation whose DeGroot links are exactly the positive weights; Bayesian agents' links are unconstrained. $(\mathbf I-\mathbf W)^{-1}$ is Mathlib's matrix inverse; Assumption 1 makes $\mathbf I-\mathbf W$ invertible, so no invertibility hypothesis is added.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Theorem 2, p. 11; model §2, pp. 5–7; Assumption 1, pp. 10–11; proof in Appendix E.2, pp. 46–47

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SocialManip.Beliefs

theorem theorem_2 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Finset (Fin n)) (θ : Fin n → ℝ) (α : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ) (q lam lamStar : ℝ) (y yhat y' : State) (x : Fin n → Bool)
    (hq : 0 < q ∧ q < 1) (hp : ∀ i, 1 / 2 ≤ p i ∧ p i < 1)
    (hlam : 0 < lam) (hlamStar : 0 < lamStar)
    (hθ : ∀ i ∉ B, 0 ≤ θ i) (hα : ∀ i ∉ B, ∀ j, 0 ≤ α i j)
    (hrow : ∀ i ∉ B, θ i + ∑ j, α i j = 1)
    (s : Fin n → ℕ → Ω → State) (hsm : ∀ i τ, Measurable (s i τ))
    (hind : ∀ i, iIndepFun (fun τ => s i τ) P)
    (hlaw : ∀ i τ, P {ω | s i τ ω = State.S} =
      ENNReal.ofReal (signalProbS (p i) lam lamStar y yhat (x i)))
    (hA1i : ∀ i, p i < (lamStar + lam) / (2 * lam))
    (adj : Fin n → Fin n → Prop) (hadj : ∀ i ∉ B, ∀ j, adj i j ↔ 0 < α i j)
    (hA1ii : ∀ i j, i ≠ j → Relation.TransGen adj i j)
    (hA1iii : ∀ i ∉ B, (0 < θ i ↔ 1 / 2 < p i))
    (hA1iv : ∃ i, 1 / 2 < p i) :
    ∃ c : Fin n → ℝ, ∀ᵐ ω ∂P,
      (∀ i, i ∉ B → Tendsto (fun t => BU (p i) q (fun τ => s i τ ω) t y') atTop (𝓝 (c i))) ∧
      ∀ π₀ : Fin n → ℝ, (∀ i ∉ B, 0 ≤ π₀ i ∧ π₀ i ≤ 1) →
        Tendsto (fun t => belief B θ α p q (fun i τ => s i τ ω) y y' π₀ t) atTop
          (𝓝 ((1 - W B α)⁻¹ *ᵥ fun i => thetaVec B θ i * (if i ∈ B then truth y y' else c i))) := by sorry

end SocialManip.Beliefs
