-- Prove2me | Theorems.Thm_TabooRegen_delay_shift
-- name    : TabooRegen.delay_shift
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-05T16:59:19.608194+00:00
-- url     : https://prove2.me/theorems/344a9f9b-7268-48b1-b643-e1e4b5bfd386
-- title:
--   Delay reduction: a delayed taboo-regenerative model reduces to its non-delayed version on $\{T(0)\le\Gamma\}$
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense (Definition 2) with $P(T(0)\le\Gamma)>0$. On $\Omega'=\{T(0)\le\Gamma\}$ with $P'=Q=P(\cdot\mid\Gamma\ge T(0))$, the time-shifted process $X'(t)=X(T(0)+t)$ with regeneration times $T'(n)=T(n)-T(0)$ is a non-delayed ($T'(0)=0$) taboo-regenerative model in the wide sense, with the same cycles $W'_n=W_n$ ($n\ge1$); it satisfies A1, A2, A3, A4, A7 exactly when $X$ does, with the same $\lambda$, the same normalizer $E\int_0^{\gamma_1\wedge\tau_1}e^{\alpha u}du$ and the same unnormalized $P^*$ window masses. Moreover, for $t\ge0$, every $k$ and measurable $B$,
--
--   $$P\big(((W_{N(t)+1+j})_{|j|\le k},\beta(t))\in B,\ N(t)\ge k,\ \Gamma>t\big)=\int_{\{T(0)\le\Gamma\}}\mathbf 1\{T(0)\le t\}\,P'\big(((W'_{N'(u)+1+j})_{|j|\le k},\beta'(u))\in B,\ N'(u)\ge k,\ \Gamma'>u\big)\Big|_{u=t-T(0)}\,dP.$$
--
--   Role: reduces the delayed case of Theorem 2 to the non-delayed (4.2) machinery, which assumes $T(0)=0$; the parent integrates the non-delayed asymptotics against the law of $T(0)$ on $\{T(0)\le\Gamma\}$.
--
--   **Formalization Note**: the non-delayed model lives on the subtype $\{\omega\mid T(0)\le\Gamma\}$ and is given existentially; its zeroth cycle is the cemetery path.
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, https://doi.org/10.1023/B:QUES.0000027987.00421.80, Definition 2 (p.275) and Theorem 2 with its proof (p.286): the delayed case by conditioning on T(0)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

theorem delay_shift {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (hP : M.P {ω | M.T 0 ω ≤ M.Γ ω} ≠ 0) :
    ∃ M' : Model S A {ω // M.T 0 ω ≤ M.Γ ω},
      M'.IsWideSenseTabooRegen ∧ (∀ ω, M'.T 0 ω = 0) ∧
      (∀ α, M'.A1 α ↔ M.A1 α) ∧ (M'.A2 ↔ M.A2) ∧ (∀ α, M'.A3 α ↔ M.A3 α) ∧
      (∀ α, M'.A4 α ↔ M.A4 α) ∧ (M'.A7 ↔ M.A7) ∧
      (∀ α, M'.rate α = M.rate α) ∧ (∀ α, M'.cycleWeight α = M.cycleWeight α) ∧
      (∀ α k (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)), M'.PstarNum α k B = M.PstarNum α k B) ∧
      ∀ (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)), MeasurableSet B → ∀ t : ℝ, 0 ≤ t →
        M.P {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧ ENNReal.ofReal t < M.Γ ω} =
          ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, (if M.T 0 ω ≤ ENNReal.ofReal t then
            M'.P {ω' | k < M'.strad (t - (M.T 0 ω).toReal) ω' ∧
              (M'.win k (t - (M.T 0 ω).toReal) ω', M'.age (t - (M.T 0 ω).toReal) ω') ∈ B ∧
              ENNReal.ofReal (t - (M.T 0 ω).toReal) < M'.Γ ω'} else 0) ∂M.P := by sorry

end TabooRegen
