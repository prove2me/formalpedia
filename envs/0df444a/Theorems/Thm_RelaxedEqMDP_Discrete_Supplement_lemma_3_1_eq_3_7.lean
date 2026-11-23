-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_Supplement_lemma_3_1_eq_3_7
-- name    : RelaxedEqMDP.Discrete.Supplement.lemma_3_1_eq_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:10:03.902623+00:00
-- url     : https://prove2.me/theorems/7e43198e-c4b4-4f08-952e-3c2308bc864a
-- title:
--   Lemma 3.1, (3.7) (corrected: uniform right continuity at zero) — first-order expansion of the concatenated value J̃^{π′⊗επ} as ε ↓ 0
-- statement:
--   Let $d,\ell>0$ and $\mathcal S=\{1,\dots,d\}$, let $U\subset\mathbb R^\ell$ be compact with $\mathrm{Leb}(U)>0$, and let each $u\in U$ carry a rate matrix $q^u$ ($q^u_{ij}\ge0$ for $j\ne i$, rows summing to $0$). Let $f(t,i,u)$ be the reward and $\delta$ the discount ($\delta:[0,\infty)\to[0,1]$ nonincreasing, $\delta(0)=1$), and assume **Assumption 3.1**: $\int_0^\infty\big(\sup_{i\in\mathcal S,u\in U}|f(s,i,u)|+\delta(s)\big)\,ds<\infty$. Assume that $t\mapsto f(t,i,u)$ is continuous on $[0,\infty)$ for every action, with right continuity at zero **uniform in $u\in U$**, that $\delta$ is continuous on $[0,\infty)$, and that the rates are bounded on $U$. Then for every $i\in\mathcal S$ and all relaxed controls $\pi,\pi'\in\Pi$,
--   $$\widetilde J^{\pi'\otimes_\varepsilon\pi}(i)=\widetilde V^\pi(\varepsilon,i)+\Big(f^{\pi'(i)}(0,i)+Q^{\pi'(i)}_i\cdot\widetilde V^\pi(\varepsilon)\Big)\varepsilon+o(\varepsilon)\qquad(\varepsilon\downarrow0),$$
--   where $\widetilde V^\pi(t,\cdot)$ is the value of $\pi$ started at time $t$ (3.4).
--
--   This unregularized expansion turns the equilibrium condition for (3.1) into the support condition of Proposition 3.2.
--
--   **Formalization Note** The hypotheses are those of Lemma 3.1, including continuity of $\delta$, although $\delta$ does not enter (3.7).
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
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 12, Lemma 3.1, (3.7); context: p. 11, (3.1), (3.4); repair evidence: p. 26, proof of Lemma 5.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- Lemma 3.1, (3.7), p. 12: under Assumption 3.1, with `t ↦ f(t,i,u)` continuous on `[0,∞)`
with right continuity at zero uniform in `u ∈ U` and `δ` continuous on `[0,∞)`, for every `i ∈ S` and `π, π′ ∈ Π`,
`J̃^{π′⊗_ε π}(i) = Ṽ^π(ε,i) + (f^{π′(i)}(0,i) + Q^{π′(i)}_i · Ṽ^π(ε)) ε + o(ε)` as `ε ↓ 0`. -/
theorem lemma_3_1_eq_3_7 {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (hS : StandingCT U q) (hqb : RatesBdd U q) (hM : MeasMapsCT U f q)
    (h31 : Assumption31 U f δ) (hfc : ∀ i, ∀ u ∈ U, ContinuousOn (fun s => f s i u) (Set.Ici 0))
    (h0 : TimeContAtZeroUnif U f) (hδc : ContinuousOn δ (Set.Ici 0)) :
    ∀ i, ∀ pol pol' : Control d ℓ, IsRelaxed U pol → IsRelaxed U pol' →
      Tendsto (fun ε : ℝ =>
          (JconcatT q f pol' pol ε i - Vt q f pol ε i -
            (fbarCT f (pol' i) 0 i + Qbar q pol' i ⬝ᵥ Vt q f pol ε) * ε) / ε)
        (𝓝[>] 0) (𝓝 0) := by sorry
end RelaxedEqMDP.Discrete.Supplement
