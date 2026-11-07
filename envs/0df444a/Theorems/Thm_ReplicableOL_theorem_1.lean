-- Prove2me | Theorems.Thm_ReplicableOL_theorem_1
-- name    : ReplicableOL.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:10.468868+00:00
-- url     : https://prove2.me/theorems/5f765460-0cdf-4f67-ab88-81d1ccb6c4b9
-- title:
--   Theorem 1 (precise form) — every $\rho$-replicable two-expert learner has regret at least $c\sqrt\Delta T^{3/4}/\sqrt\rho$ with probability at least $1/6$
-- statement:
--   Let $\rho\in(0,\frac1{100}]$, $\Delta\in(0,\frac14]$, $c_2:=9\cdot10^{-10}$,
--   $$
--   T\ge T_0(\rho,\Delta):=\max\{1.3\cdot10^{26}\rho^2\Delta^{-2},\ 1.3\cdot10^{22}(\rho\Delta)^2,\ 10^{-3}(\rho\Delta)^{-2}\}
--   $$
--   and $L:=\lceil c_2\sqrt T/(\rho\Delta)\rceil$, with $k=\lfloor T/L\rfloor$. On Construction C (epoch means $\mu_j$ i.i.d. uniform on $[-\Delta,\Delta]$, and $\ell_t=(B_t,1-B_t)$ with $B_t\sim\mathrm{Bern}(\frac12+\mu_j)$ in epoch $j$), every learner that is $\rho$-replicable under each law $P_\theta$, in particular every adversarially $\rho$-replicable learner, satisfies
--   $$
--   \mathbb P_{\theta,S,R}[\mathrm{Reg}_T\ge A/500]\ge\frac16,\qquad A=\mathbb E|X|\ge0.4556\,\Delta L\sqrt k,\qquad A/500\ge c\sqrt\Delta\,T^{3/4}/\sqrt\rho,
--   $$
--   with $c:=2.7\cdot10^{-8}$. Hence some single $P_\theta$ forces this regret with probability at least $1/6$.
--
--   More generally, if $k\ge100$ and $\Delta\sqrt L\ge100$, then for $c',\varepsilon,\delta,\nu\in(0,1)$ with $c'+\varepsilon<1$ and $B_\delta(\rho/\nu)\le\varepsilon A$,
--   $$
--   \mathbb P[\mathrm{Reg}_T\ge c'A]\ge0.1994(1-c'-\varepsilon)^{4/3}-\rho-\delta-\nu.
--   $$
--   This is the typical-case price of replicability: Hedge, which is not replicable, has regret $O(\sqrt T)$ on the same instances.
--
--   **Formalization Note** The seed space is an arbitrary probability space. The first three displayed clauses and the single-$\theta$ clause are conjuncts; $\theta$ in the single-$\theta$ clause lies in $[-\Delta,\Delta]^k$ and may depend on the learner, which the proof gives.
--
--   Differences from the source:
--   - encoding: the informal form with absolute constants $c_0,c,c_2,C$ (p.3) → the precise form of p.9 with explicit constants; reason: p.9 states this form, and it implies p.3's for $C$ large
--   - encoding: "in particular every adversarially $\rho$-replicable learner" → the hypothesis is $\rho$-replicability under each $P_\theta$, with $\theta\in[-\Delta,\Delta]^k$; `lawP_isProductLaw` gives the implication; reason: the "in particular" is a corollary of the stated hypothesis
--   - encoding: $\mathbb P_{\theta,S,R}$ → `regretProb`, an iterated `lintegral`; in the single-$\theta$ clause the measure `(lawP T L θ).prod PR`; reason: $R$ is independent of $(\theta,S)$ by (H2) and (H5)
--   - encoding: $1.3\cdot10^{26}$, $1.3\cdot10^{22}$, $10^{-3}$, $c_2$, $c$ → the exact rationals `13 * 10^25`, `13 * 10^21`, `1 / 10^3`, `9 / 10^10`, `27 / 10^9`; reason: the same numbers
--   - encoding: losses in $[0,1]^2$; a learner's maps read $[0,1]$-valued losses → loss vectors typed `Fin 2 → ℝ`, with `Learner` defined on all reals; reason: every law is carried by $[0,1]^2$, and a learner on $[0,1]$ extends measurably
--   - encoding: a probability lower bound that may be a negative real → `ENNReal.ofReal` of it; reason: when it is negative, both forms say nothing
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 1 (precise form), p.9; informal form and "some single P_θ", p.3; proof p.13

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_regret
import Definitions.Def_ReplicableOL_IsReplicableUnder
import Definitions.Def_ReplicableOL_priorBox
import Definitions.Def_ReplicableOL_lawP
import Definitions.Def_ReplicableOL_epochLen
import Definitions.Def_ReplicableOL_Tzero
import Definitions.Def_ReplicableOL_advantage
import Definitions.Def_ReplicableOL_regretProb
import Definitions.Def_ReplicableOL_Bdelta
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Theorem 1 (precise form).** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 1 (precise form), p.9; informal form and "some single P_θ", p.3; proof p.13. All clauses: `P_{θ,S,R}[Reg_T ≥ A/500] ≥ 1/6`, `A ≥ 0.4556 ΔL√k`, `A/500 ≥ c√Δ T^{3/4}/√ρ` with `c = 2.7·10⁻⁸`, the single-`θ` form ("Hence some single P_θ forces this regret", p.3, proof p.13), and the "more generally" clause.

**Formalization Note.** The learner is fixed first and then `θ, S, R` are drawn (H5); the joint probability is `regretProb`, and in the single-`θ` form `θ` may depend on the learner. Constants are explicit and global, which implies the `∃ c₀, c, c₂, C` form of p.3 for `C` large. The hypothesis is ρ-replicability under each law `P_θ`, and `lawP_isProductLaw` gives it for adversarially ρ-replicable learners. `ENNReal.ofReal` of a negative real is `0`, a true trivial bound in the general clause. -/
theorem theorem_1 {R : Type*} [MeasurableSpace R] (PR : Measure R) [IsProbabilityMeasure PR] :
    (∀ (ρ Δ : ℝ) (T : ℕ), 0 < ρ → ρ ≤ 1 / 100 → 0 < Δ → Δ ≤ 1 / 4 → Tzero ρ Δ ≤ T →
      ∀ 𝓛 : Learner 2 T R,
        (∀ θ ∈ priorBox (T / epochLen ρ Δ T) Δ,
            IsReplicableUnder 𝓛 PR ρ (lawP T (epochLen ρ Δ T) θ)) →
        ENNReal.ofReal (1 / 6) ≤
            regretProb 𝓛 PR (epochLen ρ Δ T) Δ (advantage T (epochLen ρ Δ T) Δ / 500) ∧
        0.4556 * Δ * (epochLen ρ Δ T : ℝ) * √((T / epochLen ρ Δ T : ℕ) : ℝ) ≤ advantage T (epochLen ρ Δ T) Δ ∧
        27 / 10 ^ 9 * √Δ * (T : ℝ) ^ (3 / 4 : ℝ) / √ρ ≤ advantage T (epochLen ρ Δ T) Δ / 500 ∧
        ∃ θ ∈ priorBox (T / epochLen ρ Δ T) Δ,
          ENNReal.ofReal (1 / 6) ≤
            ((lawP T (epochLen ρ Δ T) θ).prod PR)
              {p | advantage T (epochLen ρ Δ T) Δ / 500 ≤ regret 𝓛 p.1 p.2}) ∧
    (∀ (ρ Δ c' ε δ ν : ℝ) (T L : ℕ), 0 < ρ → ρ ≤ 1 / 100 → 0 < Δ → Δ ≤ 1 / 4 →
      100 ≤ T / L → 100 ≤ Δ * √(L : ℝ) →
      c' ∈ Set.Ioo (0 : ℝ) 1 → ε ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) 1 → ν ∈ Set.Ioo (0 : ℝ) 1 →
      c' + ε < 1 →
      Bdelta Δ L δ (ρ / ν) ≤ ε * advantage T L Δ →
      ∀ 𝓛 : Learner 2 T R,
        (∀ θ ∈ priorBox (T / L) Δ, IsReplicableUnder 𝓛 PR ρ (lawP T L θ)) →
        ENNReal.ofReal (0.1994 * (1 - c' - ε) ^ (4 / 3 : ℝ) - ρ - δ - ν) ≤
          regretProb 𝓛 PR L Δ (c' * advantage T L Δ)) := by sorry

end ReplicableOL
