-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_Supplement_lemma_3_1_eq_3_6
-- name    : RelaxedEqMDP.Discrete.Supplement.lemma_3_1_eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:06:03.324988+00:00
-- url     : https://prove2.me/theorems/7089ab4d-e6b6-4d7c-b565-1ab6bd086933
-- title:
--   Lemma 3.1, (3.6) (corrected: uniform right continuity at zero) — first-order expansion of the regularized concatenated value J̃^{π′⊗επ}_λ as ε ↓ 0
-- statement:
--   Let $d,\ell>0$ and $\mathcal S=\{1,\dots,d\}$, let $U\subset\mathbb R^\ell$ be compact with $\mathrm{Leb}(U)>0$, and let each $u\in U$ carry a rate matrix $q^u$ ($q^u_{ij}\ge0$ for $j\ne i$, rows summing to $0$). Let $f(t,i,u)$ be the reward and $\delta$ the discount ($\delta:[0,\infty)\to[0,1]$ nonincreasing, $\delta(0)=1$), and assume **Assumption 3.1**: $\int_0^\infty\big(\sup_{i\in\mathcal S,u\in U}|f(s,i,u)|+\delta(s)\big)\,ds<\infty$. Assume that $t\mapsto f(t,i,u)$ is continuous on $[0,\infty)$ for every action, with right continuity at zero **uniform in $u\in U$**, that $\delta$ is continuous on $[0,\infty)$, and that the rates $q^u_{ij}$ are bounded on $U$. Fix $\lambda>0$. Then for every $i\in\mathcal S$ and all $\pi,\pi'\in\Pi_r$,
--   $$\widetilde J^{\pi'\otimes_\varepsilon\pi}_\lambda(i)=\widetilde V^\pi_\lambda(\varepsilon,i)+\Big(f^{\pi'(i)}(0,i)+\lambda\mathcal H(\pi'(i))+Q^{\pi'(i)}_i\cdot\widetilde V^\pi_\lambda(\varepsilon)\Big)\varepsilon+o(\varepsilon)\qquad(\varepsilon\downarrow0).$$
--   Here $\widetilde J^{\pi'\otimes_\varepsilon\pi}_\lambda$ is the entropy-regularized value of the control that uses $\pi'$ on $[0,\varepsilon)$ and $\pi$ afterwards, $\widetilde V^\pi_\lambda(t,\cdot)$ is the regularized value of $\pi$ started at time $t$ (3.5), $\mathcal H$ is the differential entropy, and $Q^{\pi'(i)}_i=\int_Uq^u_i\,\pi'(i)(du)$.
--
--   The expansion is the continuous-time counterpart of the one-step identity of the base mission (display on p. 6), and it turns the equilibrium condition (3.3) into a pointwise maximization (Proposition 3.1).
--
--   **Formalization Note** The $o(\varepsilon)$ is the statement that the remainder divided by $\varepsilon$ tends to $0$ as $\varepsilon\downarrow0$; the bracket contains $\widetilde V^\pi_\lambda(\varepsilon)$, as printed.
--
--   Differences from the source:
--   - correction: f(·, i, u) continuous on [0, ∞) for each i and u (Lemma 3.1, Proposition 3.1, Corollary 3.1; Proposition 3.2 states no time continuity) → added: right continuity of t ↦ f(t,i,u) at zero uniformly over u ∈ U (TimeContAtZeroUnif); the printed pointwise time continuity on [0,∞) is retained; reason: The moving action-bump counterexample in DISPROOF.md §1 satisfies all printed hypotheses but prevents interchange of averaging over actions with the time-zero limit. The additional uniform right continuity at zero bounds the averaged remainder by ε times a quantity tending to zero, as needed in (3.6)–(3.7) and (A.14)–(A.17). No uniform continuity at positive times is imposed. It excludes the moving-bump example; joint continuity or pointwise time continuity together with Assumption 2.2 implies it on compact U.
--   - reading: the relaxed rate matrix Q^µ_ij := ∫_U q^u_ij µ(du), defined for every µ ∈ 𝒫(U) (p. 10) → the rates are bounded on U (RatesBdd: |q^u_ij| ≤ C for u ∈ U); reason: for measurable q, ∫|q^u_ij|µ(du) < ∞ for every probability µ on U holds exactly when q is bounded on U; Theorems 3.1, 3.2 and 5.1 get it from Assumption 2.2 and compactness and do not carry it
--   - reading: the integrals f^µ(t,i) = ∫_U f(t,i,u)µ(du), Q^µ_ij = ∫_U q^u_ij µ(du) and the time integrals (3.1)–(3.5), with no measurability stated → (s,u) ↦ f(s,i,u) measurable on [0,∞) × U and u ↦ q^u_ij measurable on U (MeasMapsCT U f q); reason: the integrals presuppose it; it is the standing measurability convention, as in the base mission's MeasMaps
--   - reading: ℓ ∈ ℕ and S = {1, …, d} with d ∈ ℕ (p. 4, reused in §3) → 0 < ℓ and 0 < d; reason: The source uses positive natural dimensions; Fin d indexes the d states from zero instead of one.
--   - encoding: f : [0,∞) × S × U → ℝ, δ : [0,∞) → [0,1] → f : ℝ → Fin d → A ℓ → ℝ and δ : ℝ → ℝ, with every hypothesis and integral restricted to times s ≥ 0 and actions u ∈ U; reason: The values outside the source domain do not enter the hypotheses or the values of admissible controls; measurability is stated on the source-domain subtypes.
--   - encoding: values (3.1), (3.2), (3.4), (3.5) as expectations E_i[∫_0^∞ … ds] over the controlled chain X^π → ∫_0^∞ (exp(sQ^π) r(s))_i ds with Q^π the relaxed generator (rows Q^{π(i)}_i) and r(s) the vector of averaged rewards; reason: the law of X^π_s started at i is row i of exp(sQ^π), the continuous-time analogue of Remark 2.1; the values are the same
--   - encoding: J̃^{π′⊗_επ} for the control that uses π′ on [0, ε) and π on [ε, ∞) → ∫_0^ε (exp(sQ^{π′}) r^{π′}(s))_i ds + (exp(εQ^{π′}) Ṽ^π(ε))_i (and the same with r_λ and Ṽ_λ); reason: this is the value of the concatenation by the Markov property at time ε; no process is constructed
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 12, Lemma 3.1, (3.6); context: p. 11, (3.2), (3.5), Assumption 3.1; repair evidence: p. 26, proof of Lemma 5.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- Lemma 3.1, (3.6), p. 12: under Assumption 3.1, with `t ↦ f(t,i,u)` continuous on `[0,∞)`
with right continuity at zero uniform in `u ∈ U` and `δ` continuous on `[0,∞)`, for every `λ > 0`, `i ∈ S` and
`π, π′ ∈ Π_r`,
`J̃^{π′⊗_ε π}_λ(i) = Ṽ^π_λ(ε,i) + (f^{π′(i)}(0,i) + λℋ(π′(i)) + Q^{π′(i)}_i · Ṽ^π_λ(ε)) ε + o(ε)`
as `ε ↓ 0`. -/
theorem lemma_3_1_eq_3_6 {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (hS : StandingCT U q) (hqb : RatesBdd U q) (hM : MeasMapsCT U f q)
    (h31 : Assumption31 U f δ) (hfc : ∀ i, ∀ u ∈ U, ContinuousOn (fun s => f s i u) (Set.Ici 0))
    (h0 : TimeContAtZeroUnif U f) (hδc : ContinuousOn δ (Set.Ici 0))
    (lam : ℝ) (hlam : 0 < lam) :
    ∀ i, ∀ pol pol' : Control d ℓ, IsRegular U pol → IsRegular U pol' →
      Tendsto (fun ε : ℝ =>
          (JlamConcatT U q f δ lam pol' pol ε i - Vlamt U q f δ lam pol ε i -
            (fbarCT f (pol' i) 0 i + lam * ent U (pol' i) +
              Qbar q pol' i ⬝ᵥ Vlamt U q f δ lam pol ε) * ε) / ε)
        (𝓝[>] 0) (𝓝 0) := by sorry
end RelaxedEqMDP.Discrete.Supplement
