-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_Supplement_theorem_3_1
-- name    : RelaxedEqMDP.Discrete.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:09:01.376598+00:00
-- url     : https://prove2.me/theorems/d491b467-45a7-4b67-8924-f34c0bb76fde
-- title:
--   Theorem 3.1 — in continuous time, for every λ > 0, Ψ̃λ has a fixed point y and Γ̃λ(y,·) is a regular relaxed equilibrium for (3.2)
-- statement:
--   Let $d,\ell>0$ and $\mathcal S=\{1,\dots,d\}$, let $U\subset\mathbb R^\ell$ be compact with $\mathrm{Leb}(U)>0$, and let each $u\in U$ carry a rate matrix $q^u$ ($q^u_{ij}\ge0$ for $j\ne i$, rows summing to $0$). Let $f(t,i,u)$ be the reward and $\delta$ the discount ($\delta:[0,\infty)\to[0,1]$ nonincreasing, $\delta(0)=1$), and assume **Assumption 3.1**: $\int_0^\infty\big(\sup_{i\in\mathcal S,u\in U}|f(s,i,u)|+\delta(s)\big)\,ds<\infty$. Assume **Assumption 2.2** with $q$ in place of $p$: for some $\Theta>0$, $|f(t,i,u_1)-f(t,i,u_2)|+|q^{u_1}_i-q^{u_2}_i|\le\Theta|u_1-u_2|$ for all $t\ge0$, $i$ and $u_1,u_2\in U$; and **Assumption 2.3**: a uniform cone condition on $U$ with half-angle $\iota\in(0,\pi/2]$ and height $\vartheta>0$. Suppose that $f(\cdot,i,u)$ and $\delta$ are continuous on $[0,\infty)$. Then for every $\lambda>0$ there is $y\in\mathbb R^d$ with
--   $$\widetilde\Psi_\lambda(y)=y,$$
--   and the Gibbs control $\widetilde\Gamma_\lambda(y,\cdot)\in\Pi_r$ is a regular relaxed equilibrium for the entropy-regularized problem (3.2).
--
--   This is the existence result for the regularized continuous-time problem, the analogue of the base mission's Theorem 2.1; Theorem 3.2 takes $\lambda\downarrow0$ in it.
--
--   **Formalization Note** Both conclusions are stated for the same $y$. The equilibrium includes membership of $\Pi_r$.
--
--   Differences from the source:
--   - reading: Assumption 2.2 'with p^u_i therein replaced by q^u_i': sup of |f(t,i,u₁) − f(t,i,u₂)| + |q^{u₁}_i − q^{u₂}_i| over |u₁ − u₂| finite, uniformly in t → Assumption22CT: Θ > 0 with |f(t,i,u₁) − f(t,i,u₂)| + |q^{u₁}_i − q^{u₂}_i| ≤ Θ|u₁ − u₂| for all t ≥ 0, i and u₁, u₂ ∈ U (Euclidean norms); reason: (2.16) with q for p, over the continuous time set [0,∞); a positive bound exists whenever the supremum is finite
--   - reading: Assumption 2.3: a cone with vertex u, half-angle ι and height ϑ inside U (Δ_ι printed as a double cone) → the published base Assumption23: a one-nappe cone {v : ⟨v − u, a⟩ ≥ |v − u| cos ι} cut by the open ball B_ϑ(u); reason: the base mission's disclosed reading of Assumption 2.3, reused unchanged
--   - reading: the integrals f^µ(t,i) = ∫_U f(t,i,u)µ(du), Q^µ_ij = ∫_U q^u_ij µ(du) and the time integrals (3.1)–(3.5), with no measurability stated → (s,u) ↦ f(s,i,u) measurable on [0,∞) × U and u ↦ q^u_ij measurable on U (MeasMapsCT U f q); reason: the integrals presuppose it; it is the standing measurability convention, as in the base mission's MeasMaps
--   - reading: ℓ ∈ ℕ and S = {1, …, d} with d ∈ ℕ (p. 4, reused in §3) → 0 < ℓ and 0 < d; reason: The source uses positive natural dimensions; Fin d indexes the d states from zero instead of one.
--   - encoding: f : [0,∞) × S × U → ℝ, δ : [0,∞) → [0,1] → f : ℝ → Fin d → A ℓ → ℝ and δ : ℝ → ℝ, with every hypothesis and integral restricted to times s ≥ 0 and actions u ∈ U; reason: The values outside the source domain do not enter the hypotheses or the values of admissible controls; measurability is stated on the source-domain subtypes.
--   - encoding: values (3.1), (3.2), (3.4), (3.5) as expectations E_i[∫_0^∞ … ds] over the controlled chain X^π → ∫_0^∞ (exp(sQ^π) r(s))_i ds with Q^π the relaxed generator (rows Q^{π(i)}_i) and r(s) the vector of averaged rewards; reason: the law of X^π_s started at i is row i of exp(sQ^π), the continuous-time analogue of Remark 2.1; the values are the same
--   - encoding: J̃^{π′⊗_επ} for the control that uses π′ on [0, ε) and π on [ε, ∞) → ∫_0^ε (exp(sQ^{π′}) r^{π′}(s))_i ds + (exp(εQ^{π′}) Ṽ^π(ε))_i (and the same with r_λ and Ṽ_λ); reason: this is the value of the concatenation by the Markov property at time ε; no process is constructed
--   - encoding: lim sup_{ε↓0} (J̃^{π′⊗_επ}(i) − J̃^π(i))/ε ≤ 0 in Definition 3.1 → for every η > 0 the quotient is ≤ η for all sufficiently small ε > 0; reason: equivalent to lim sup ≤ 0, and avoids Filter.limsup on ℝ, which returns a junk value for unbounded functions
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 12, Theorem 3.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- Theorem 3.1, p. 12: under Assumptions 3.1, 2.2 (with `q^u_i` for `p^u_i`) and 2.3, with
`f(·,i,u)` and `δ(·)` continuous on `[0,∞)`, for any `λ > 0` there is `y ∈ ℝ^d` with
`Ψ̃_λ(y) = y`; hence `Γ̃_λ(y,·) ∈ Π_r` is a regular relaxed equilibrium for (3.2). -/
theorem theorem_3_1 {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (Theta iota vartheta : ℝ) (hS : StandingCT U q) (hM : MeasMapsCT U f q)
    (h31 : Assumption31 U f δ) (h22 : Assumption22CT U f q Theta)
    (h23 : Assumption23 U iota vartheta)
    (hfc : ∀ i, ∀ u ∈ U, ContinuousOn (fun s => f s i u) (Set.Ici 0))
    (hδc : ContinuousOn δ (Set.Ici 0)) (lam : ℝ) (hlam : 0 < lam) :
    ∃ y : Fin d → ℝ, PsiLamCT U q f δ lam y = y ∧
      IsRegularRelaxedEqCT U q f δ lam (gibbsCtrlCT U q f lam y) := by sorry
end RelaxedEqMDP.Discrete.Supplement
