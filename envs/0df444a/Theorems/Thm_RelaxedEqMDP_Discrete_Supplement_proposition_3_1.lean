-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_Supplement_proposition_3_1
-- name    : RelaxedEqMDP.Discrete.Supplement.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:07:11.828228+00:00
-- url     : https://prove2.me/theorems/83d03b15-1846-4526-8c9c-236f9297827b
-- title:
--   Proposition 3.1 (corrected: uniform right continuity at zero) — regular relaxed equilibria in continuous time are exactly the fixed points of Φ̃λ
-- statement:
--   Let $d,\ell>0$ and $\mathcal S=\{1,\dots,d\}$, let $U\subset\mathbb R^\ell$ be compact with $\mathrm{Leb}(U)>0$, and let each $u\in U$ carry a rate matrix $q^u$ ($q^u_{ij}\ge0$ for $j\ne i$, rows summing to $0$). Let $f(t,i,u)$ be the reward and $\delta$ the discount ($\delta:[0,\infty)\to[0,1]$ nonincreasing, $\delta(0)=1$), and assume **Assumption 3.1**: $\int_0^\infty\big(\sup_{i\in\mathcal S,u\in U}|f(s,i,u)|+\delta(s)\big)\,ds<\infty$. Assume that $t\mapsto f(t,i,u)$ is continuous on $[0,\infty)$ for every action, with right continuity at zero **uniform in $u\in U$**, that $\delta$ is continuous on $[0,\infty)$, and that the rates are bounded on $U$. For every $\lambda>0$ and every $\pi\in\Pi_r$,
--   $$\pi\ \text{is a regular relaxed equilibrium for (3.2)}\iff\widetilde\Phi_\lambda(\pi)=\pi,$$
--   where $\widetilde\Phi_\lambda(\pi)=\widetilde\Gamma_\lambda(\widetilde J^\pi_\lambda,\cdot)$ is the control whose state-$i$ law has the Gibbs density
--   $$\widetilde\Gamma_\lambda(y,i)(u)=\frac{e^{\frac1\lambda(f(0,i,u)+q^u_i\cdot y)}}{\int_Ue^{\frac1\lambda(f(0,i,v)+q^v_i\cdot y)}dv},\qquad y=\widetilde J^\pi_\lambda .$$
--   A regular relaxed equilibrium is a $\pi\in\Pi_r$ with $\limsup_{\varepsilon\downarrow0}\big(\widetilde J^{\pi'\otimes_\varepsilon\pi}_\lambda(i)-\widetilde J^\pi_\lambda(i)\big)/\varepsilon\le0$ for all $\pi'\in\Pi_r$ and $i$ (Definition 3.1).
--
--   This fixed-point characterization reduces the existence of a regular relaxed equilibrium to a fixed point of a map on $\mathbb R^d$ (Corollary 3.1, Theorem 3.1).
--
--   **Formalization Note** $\widetilde\Phi_\lambda(\pi)=\pi$ is an equality of controls: for every state the two probability measures on $U$ coincide.
--
--   Differences from the source:
--   - correction: f(·, i, u) continuous on [0, ∞) for each i and u (Lemma 3.1, Proposition 3.1, Corollary 3.1; Proposition 3.2 states no time continuity) → added: right continuity of t ↦ f(t,i,u) at zero uniformly over u ∈ U (TimeContAtZeroUnif); the printed pointwise time continuity on [0,∞) is retained; reason: The moving action-bump counterexample in DISPROOF.md §1 satisfies all printed hypotheses but prevents interchange of averaging over actions with the time-zero limit. The additional uniform right continuity at zero bounds the averaged remainder by ε times a quantity tending to zero, as needed in (3.6)–(3.7) and (A.14)–(A.17). No uniform continuity at positive times is imposed. It excludes the moving-bump example; joint continuity or pointwise time continuity together with Assumption 2.2 implies it on compact U.
--   - reading: the relaxed rate matrix Q^µ_ij := ∫_U q^u_ij µ(du), defined for every µ ∈ 𝒫(U) (p. 10) → the rates are bounded on U (RatesBdd: |q^u_ij| ≤ C for u ∈ U); reason: for measurable q, ∫|q^u_ij|µ(du) < ∞ for every probability µ on U holds exactly when q is bounded on U; Theorems 3.1, 3.2 and 5.1 get it from Assumption 2.2 and compactness and do not carry it
--   - reading: the integrals f^µ(t,i) = ∫_U f(t,i,u)µ(du), Q^µ_ij = ∫_U q^u_ij µ(du) and the time integrals (3.1)–(3.5), with no measurability stated → (s,u) ↦ f(s,i,u) measurable on [0,∞) × U and u ↦ q^u_ij measurable on U (MeasMapsCT U f q); reason: the integrals presuppose it; it is the standing measurability convention, as in the base mission's MeasMaps
--   - reading: ℓ ∈ ℕ and S = {1, …, d} with d ∈ ℕ (p. 4, reused in §3) → 0 < ℓ and 0 < d; reason: The source uses positive natural dimensions; Fin d indexes the d states from zero instead of one.
--   - encoding: f : [0,∞) × S × U → ℝ, δ : [0,∞) → [0,1] → f : ℝ → Fin d → A ℓ → ℝ and δ : ℝ → ℝ, with every hypothesis and integral restricted to times s ≥ 0 and actions u ∈ U; reason: The values outside the source domain do not enter the hypotheses or the values of admissible controls; measurability is stated on the source-domain subtypes.
--   - encoding: values (3.1), (3.2), (3.4), (3.5) as expectations E_i[∫_0^∞ … ds] over the controlled chain X^π → ∫_0^∞ (exp(sQ^π) r(s))_i ds with Q^π the relaxed generator (rows Q^{π(i)}_i) and r(s) the vector of averaged rewards; reason: the law of X^π_s started at i is row i of exp(sQ^π), the continuous-time analogue of Remark 2.1; the values are the same
--   - encoding: J̃^{π′⊗_επ} for the control that uses π′ on [0, ε) and π on [ε, ∞) → ∫_0^ε (exp(sQ^{π′}) r^{π′}(s))_i ds + (exp(εQ^{π′}) Ṽ^π(ε))_i (and the same with r_λ and Ṽ_λ); reason: this is the value of the concatenation by the Markov property at time ε; no process is constructed
--   - encoding: lim sup_{ε↓0} (J̃^{π′⊗_επ}(i) − J̃^π(i))/ε ≤ 0 in Definition 3.1 → for every η > 0 the quotient is ≤ η for all sufficiently small ε > 0; reason: equivalent to lim sup ≤ 0, and avoids Filter.limsup on ℝ, which returns a junk value for unbounded functions
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 12, Proposition 3.1 (proof: pp. 23–24, Appendix A.5); repair evidence: p. 26, proof of Lemma 5.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- Proposition 3.1, p. 12: under Assumption 3.1, with `t ↦ f(t,i,u)` continuous on `[0,∞)`
with right continuity at zero uniform in `u ∈ U` and `δ` continuous on `[0,∞)`, for any `λ > 0`, `π ∈ Π_r` is a regular
relaxed equilibrium for (3.2) iff `Φ̃_λ(π) = π`. -/
theorem proposition_3_1 {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (hS : StandingCT U q) (hqb : RatesBdd U q) (hM : MeasMapsCT U f q)
    (h31 : Assumption31 U f δ) (hfc : ∀ i, ∀ u ∈ U, ContinuousOn (fun s => f s i u) (Set.Ici 0))
    (h0 : TimeContAtZeroUnif U f) (hδc : ContinuousOn δ (Set.Ici 0))
    (lam : ℝ) (hlam : 0 < lam) :
    ∀ pol : Control d ℓ, IsRegular U pol →
      (IsRegularRelaxedEqCT U q f δ lam pol ↔ PhiLamCT U q f δ lam pol = pol) := by sorry
end RelaxedEqMDP.Discrete.Supplement
