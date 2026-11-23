-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_Supplement_theorem_3_2
-- name    : RelaxedEqMDP.Discrete.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:11:18.623808+00:00
-- url     : https://prove2.me/theorems/f7ec0c20-0d45-434b-882e-bcf53d979b87
-- title:
--   Theorem 3.2 (corrected: added continuity of f in time) — a relaxed equilibrium for the continuous-time problem (3.1) exists
-- statement:
--   Let $d,\ell>0$ and $\mathcal S=\{1,\dots,d\}$, let $U\subset\mathbb R^\ell$ be compact with $\mathrm{Leb}(U)>0$, and let each $u\in U$ carry a rate matrix $q^u$ ($q^u_{ij}\ge0$ for $j\ne i$, rows summing to $0$). Let $f(t,i,u)$ be the reward and $\delta$ the discount ($\delta:[0,\infty)\to[0,1]$ nonincreasing, $\delta(0)=1$), and assume **Assumption 3.1**: $\int_0^\infty\big(\sup_{i\in\mathcal S,u\in U}|f(s,i,u)|+\delta(s)\big)\,ds<\infty$. Assume **Assumption 2.2** with $q$ in place of $p$ (a constant $\Theta>0$ with $|f(t,i,u_1)-f(t,i,u_2)|+|q^{u_1}_i-q^{u_2}_i|\le\Theta|u_1-u_2|$ for all $t\ge0$, $i$, $u_1,u_2\in U$) and **Assumption 2.3** (uniform cone condition on $U$), and suppose that $f(\cdot,i,u)$ is right continuous at zero uniformly over $u\in U$ for each $i$. Then there is a relaxed control $\pi\in\Pi$ such that
--   $$\limsup_{\varepsilon\downarrow0}\frac{\widetilde J^{\pi'\otimes_\varepsilon\pi}(i)-\widetilde J^\pi(i)}{\varepsilon}\le0\qquad\text{for all }\pi'\in\Pi\text{ and }i\in\mathcal S,$$
--   that is, a relaxed equilibrium for (3.1) exists.
--
--   This is the continuous-time counterpart of the base mission's goal, Theorem 2.2: no convexity of $U$ and no concavity of the reward are assumed.
--
--   Differences from the source:
--   - correction: Theorem 3.2 assumes Assumptions 3.1, 2.2 (with q for p) and 2.3, and no continuity of f in time → added: right continuity of f(·,i,u) at zero uniformly over u ∈ U (TimeContAtZeroUnif); reason: The oscillating-block counterexample in DISPROOF.md §2 satisfies every printed assumption but has no relaxed equilibrium. The time-zero expansions (3.6)–(3.7), which underpin the proof on p. 13, require convergence of averaged rewards at zero. Uniform right continuity at zero supplies this, while retaining measurable integrable rewards with discontinuities at positive times. No continuity of δ is added because it does not enter (3.1).
--   - reading: Assumption 2.2 'with p^u_i therein replaced by q^u_i': sup of |f(t,i,u₁) − f(t,i,u₂)| + |q^{u₁}_i − q^{u₂}_i| over |u₁ − u₂| finite, uniformly in t → Assumption22CT: Θ > 0 with |f(t,i,u₁) − f(t,i,u₂)| + |q^{u₁}_i − q^{u₂}_i| ≤ Θ|u₁ − u₂| for all t ≥ 0, i and u₁, u₂ ∈ U (Euclidean norms); reason: (2.16) with q for p, over the continuous time set [0,∞); a positive bound exists whenever the supremum is finite
--   - reading: Assumption 2.3: a cone with vertex u, half-angle ι and height ϑ inside U (Δ_ι printed as a double cone) → the published base Assumption23: a one-nappe cone {v : ⟨v − u, a⟩ ≥ |v − u| cos ι} cut by the open ball B_ϑ(u); reason: the base mission's disclosed reading of Assumption 2.3, reused unchanged
--   - reading: the integrals f^µ(t,i) = ∫_U f(t,i,u)µ(du), Q^µ_ij = ∫_U q^u_ij µ(du) and the time integrals (3.1)–(3.5), with no measurability stated → (s,u) ↦ f(s,i,u) measurable on [0,∞) × U and u ↦ q^u_ij measurable on U (MeasMapsCT U f q); reason: the integrals presuppose it; it is the standing measurability convention, as in the base mission's MeasMaps
--   - reading: ℓ ∈ ℕ and S = {1, …, d} with d ∈ ℕ (p. 4, reused in §3) → 0 < ℓ and 0 < d; reason: The source uses positive natural dimensions; Fin d indexes the d states from zero instead of one.
--   - encoding: f : [0,∞) × S × U → ℝ, δ : [0,∞) → [0,1] → f : ℝ → Fin d → A ℓ → ℝ and δ : ℝ → ℝ, with every hypothesis and integral restricted to times s ≥ 0 and actions u ∈ U; reason: The values outside the source domain do not enter the hypotheses or the values of admissible controls; measurability is stated on the source-domain subtypes.
--   - encoding: values (3.1), (3.2), (3.4), (3.5) as expectations E_i[∫_0^∞ … ds] over the controlled chain X^π → ∫_0^∞ (exp(sQ^π) r(s))_i ds with Q^π the relaxed generator (rows Q^{π(i)}_i) and r(s) the vector of averaged rewards; reason: the law of X^π_s started at i is row i of exp(sQ^π), the continuous-time analogue of Remark 2.1; the values are the same
--   - encoding: J̃^{π′⊗_επ} for the control that uses π′ on [0, ε) and π on [ε, ∞) → ∫_0^ε (exp(sQ^{π′}) r^{π′}(s))_i ds + (exp(εQ^{π′}) Ṽ^π(ε))_i (and the same with r_λ and Ṽ_λ); reason: this is the value of the concatenation by the Markov property at time ε; no process is constructed
--   - encoding: lim sup_{ε↓0} (J̃^{π′⊗_επ}(i) − J̃^π(i))/ε ≤ 0 in Definition 3.1 → for every η > 0 the quotient is ≤ η for all sufficiently small ε > 0; reason: equivalent to lim sup ≤ 0, and avoids Filter.limsup on ℝ, which returns a junk value for unbounded functions
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 13, Theorem 3.2; repair evidence: p. 12, Lemma 3.1 and Theorem 3.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- Theorem 3.2, p. 13 (corrected): under Assumptions 3.1, 2.2 (with `q^u_i` for `p^u_i`) and
2.3, and (added) right continuity of `f(·,i,u)` at zero, uniformly over `u ∈ U`, a relaxed equilibrium for (3.1) exists. -/
theorem theorem_3_2 {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (Theta iota vartheta : ℝ) (hS : StandingCT U q) (hM : MeasMapsCT U f q)
    (h31 : Assumption31 U f δ) (h22 : Assumption22CT U f q Theta)
    (h23 : Assumption23 U iota vartheta)
    (hfc : TimeContAtZeroUnif U f) :
    ∃ pol : Control d ℓ, IsRelaxedEqCT U q f pol := by sorry
end RelaxedEqMDP.Discrete.Supplement
