-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_Supplement_proposition_3_2
-- name    : RelaxedEqMDP.Discrete.Supplement.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:10:48.689807+00:00
-- url     : https://prove2.me/theorems/e4e11c5a-9664-407a-8df1-23652dc3013c
-- title:
--   Proposition 3.2 (corrected: added time continuity of f uniform in u) — relaxed equilibria in continuous time are the fixed points of Φ̃ and Ψ̃
-- statement:
--   Let $d,\ell>0$ and $\mathcal S=\{1,\dots,d\}$, let $U\subset\mathbb R^\ell$ be compact with $\mathrm{Leb}(U)>0$, and let each $u\in U$ carry a rate matrix $q^u$ ($q^u_{ij}\ge0$ for $j\ne i$, rows summing to $0$). Let $f(t,i,u)$ be the reward and $\delta$ the discount ($\delta:[0,\infty)\to[0,1]$ nonincreasing, $\delta(0)=1$), and assume **Assumption 3.1**: $\int_0^\infty\big(\sup_{i\in\mathcal S,u\in U}|f(s,i,u)|+\delta(s)\big)\,ds<\infty$. Assume that $u\mapsto f(t,i,u)$ and $u\mapsto q^u_i$ are continuous on $U$, and in addition that $t\mapsto f(t,i,u)$ is right continuous at zero **uniformly in $u\in U$**. Let $\widetilde E(y,i)=\arg\max_{u\in U}\{f(0,i,u)+q^u_i\cdot y\}$, $\widetilde\Gamma(y)=\{\pi\in\Pi:\operatorname{supp}\pi(i)\subseteq\widetilde E(y,i)\ \forall i\}$, $\widetilde\Psi(y)=\{\widetilde J^\pi:\pi\in\widetilde\Gamma(y)\}$ and $\widetilde\Phi(\pi)=\widetilde\Gamma(\widetilde J^\pi)$. Then:
--
--   1. for every $\pi\in\Pi$,
--   $$\pi\ \text{is a relaxed equilibrium for (3.1)}\iff\pi\in\widetilde\Phi(\pi);\tag{3.12}$$
--   2. for every $y\in\mathbb R^d$, $y=\widetilde J^\pi$ for some relaxed equilibrium $\pi\in\Pi$ if and only if $y\in\widetilde\Psi(y)$.
--
--   A relaxed equilibrium is a $\pi\in\Pi$ with $\limsup_{\varepsilon\downarrow0}\big(\widetilde J^{\pi'\otimes_\varepsilon\pi}(i)-\widetilde J^\pi(i)\big)/\varepsilon\le0$ for all $\pi'\in\Pi$ and $i$ (Definition 3.1). The characterization identifies the limits in Theorem 3.2 and Theorem 5.1 (b) as equilibria.
--
--   **Formalization Note** The support condition $\operatorname{supp}\pi(i)\subseteq\widetilde E(y,i)$ is written $\pi(i)\big(\widetilde E(y,i)^{\mathrm c}\big)=0$, as in the base mission.
--
--   Differences from the source:
--   - correction: no continuity of f in time (Proposition 3.2 assumes only that u ↦ f(t,i,u) and u ↦ q^u_i are continuous) → added: right continuity of t ↦ f(t,i,u) at zero uniformly over u ∈ U (TimeContAtZeroUnif); reason: The moving action-bump counterexample in DISPROOF.md §1 satisfies all printed hypotheses but prevents interchange of averaging over actions with the time-zero limit. The additional uniform right continuity at zero bounds the averaged remainder by ε times a quantity tending to zero, as needed in (3.6)–(3.7) and (A.14)–(A.17). No uniform continuity at positive times is imposed. It excludes the moving-bump example; joint continuity or pointwise time continuity together with Assumption 2.2 implies it on compact U.
--   - correction: (3.10): Γ̃(y) := {π ∈ Π : supp(π(i)) ⊆ E(y, i), ∀i ∈ S} with the discrete E of (2.20) → supp(π(i)) ⊆ Ẽ(y, i) of (3.9), written as π(i)(Ẽ(y, i)ᶜ) = 0; reason: misprint: (3.9) defines Ẽ just above, and the proof of Proposition 3.2 (p. 13) and (A.24) (p. 27) use Ẽ; the support condition is the base mission's reading of supp ⊆ E
--   - encoding: u ↦ f(t, i, u) and u ↦ q^u_i continuous → continuous on U, for every t ≥ 0, i and every entry q^u_ij; reason: f and q are defined on [0,∞) × S × U; a row is continuous iff each entry is
--   - reading: the integrals f^µ(t,i) = ∫_U f(t,i,u)µ(du), Q^µ_ij = ∫_U q^u_ij µ(du) and the time integrals (3.1)–(3.5), with no measurability stated → (s,u) ↦ f(s,i,u) measurable on [0,∞) × U and u ↦ q^u_ij measurable on U (MeasMapsCT U f q); reason: the integrals presuppose it; it is the standing measurability convention, as in the base mission's MeasMaps
--   - reading: ℓ ∈ ℕ and S = {1, …, d} with d ∈ ℕ (p. 4, reused in §3) → 0 < ℓ and 0 < d; reason: The source uses positive natural dimensions; Fin d indexes the d states from zero instead of one.
--   - encoding: f : [0,∞) × S × U → ℝ, δ : [0,∞) → [0,1] → f : ℝ → Fin d → A ℓ → ℝ and δ : ℝ → ℝ, with every hypothesis and integral restricted to times s ≥ 0 and actions u ∈ U; reason: The values outside the source domain do not enter the hypotheses or the values of admissible controls; measurability is stated on the source-domain subtypes.
--   - encoding: values (3.1), (3.2), (3.4), (3.5) as expectations E_i[∫_0^∞ … ds] over the controlled chain X^π → ∫_0^∞ (exp(sQ^π) r(s))_i ds with Q^π the relaxed generator (rows Q^{π(i)}_i) and r(s) the vector of averaged rewards; reason: the law of X^π_s started at i is row i of exp(sQ^π), the continuous-time analogue of Remark 2.1; the values are the same
--   - encoding: J̃^{π′⊗_επ} for the control that uses π′ on [0, ε) and π on [ε, ∞) → ∫_0^ε (exp(sQ^{π′}) r^{π′}(s))_i ds + (exp(εQ^{π′}) Ṽ^π(ε))_i (and the same with r_λ and Ṽ_λ); reason: this is the value of the concatenation by the Markov property at time ε; no process is constructed
--   - encoding: lim sup_{ε↓0} (J̃^{π′⊗_επ}(i) − J̃^π(i))/ε ≤ 0 in Definition 3.1 → for every η > 0 the quotient is ≤ η for all sufficiently small ε > 0; reason: equivalent to lim sup ≤ 0, and avoids Filter.limsup on ℝ, which returns a junk value for unbounded functions
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 13, Proposition 3.2 and (3.9)–(3.12); repair evidence: p. 12, Lemma 3.1 and p. 26, proof of Lemma 5.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- Proposition 3.2, p. 13 (corrected): under Assumption 3.1, with `u ↦ f(t,i,u)` and
`u ↦ q^u_i` continuous on `U`, and (added) right continuity of `t ↦ f(t,i,u)` at zero uniformly in
`u ∈ U`: `π ∈ Π` is a relaxed equilibrium for (3.1) iff `π ∈ Φ̃(π)` (3.12); moreover, for any
`y ∈ ℝ^d`, `y = J̃^π` for some relaxed equilibrium `π ∈ Π` iff `y ∈ Ψ̃(y)`. -/
theorem proposition_3_2 {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (hS : StandingCT U q) (hM : MeasMapsCT U f q) (h31 : Assumption31 U f δ)
    (hfu : ∀ t, 0 ≤ t → ∀ i, ContinuousOn (f t i) U)
    (hqu : ∀ i j, ContinuousOn (fun u => q u i j) U)
    (hfc : TimeContAtZeroUnif U f) :
    (∀ pol : Control d ℓ, IsRelaxed U pol →
        (IsRelaxedEqCT U q f pol ↔ pol ∈ PhiSetCT U q f pol)) ∧
      ∀ y : Fin d → ℝ,
        (∃ pol : Control d ℓ, IsRelaxedEqCT U q f pol ∧ y = Jt q f pol) ↔
          y ∈ PsiSetCT U q f y := by sorry
end RelaxedEqMDP.Discrete.Supplement
