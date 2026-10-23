-- Prove2me | Theorems.Thm_RiskFunctionals_ValueOfInfo_value_of_information_supermartingale
-- name    : RiskFunctionals.ValueOfInfo.value_of_information_supermartingale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:31.046753+00:00
-- url     : https://prove2.me/theorems/640bd31f-e372-498d-a24b-c38e319650ab
-- title:
--   Corollary 5.3 — the value-of-information process is a supermartingale
-- statement:
--   Let $(\nu_t)_{t=0,\dots,T}$ be a tree process on $(\Omega,\mathcal F,P)$ with finitely many nodes at each stage and a single root node at $t=0$, with standard filtration $\mathcal F_t=\sigma(\nu_t)$. Let $\xi_t=f_t(\nu_t)$ be the scenario variables, $H(x,\xi)$ a measurable profit function, $\mathcal X$ the decision space and $\mathcal A$ a version-independent acceptability functional with domain $\mathcal D$, which contains the law of $H(x,\xi)$ under $P^{\{\nu_t=v\}}$ for every feasible clairvoyant decision $x$ ($x\lhd\boldsymbol{\mathcal F}^T$, $x\in\mathcal X$) and every node $v$ with $P\{\nu_t=v\}>0$. For every stage $t$ and every node $v$ with $P\{\nu_t=v\}>0$ suppose both conditional problems attain their maxima
--   $$A_t(v)=\max\{\mathcal A_{P^{\{\nu_t=v\}}}[H(x,\xi)] : x\lhd\boldsymbol{\mathcal F},\ x\in\mathcal X\},\qquad C_t(v)=\max\{\mathcal A_{P^{\{\nu_t=v\}}}[H(x,\xi)] : x\lhd\boldsymbol{\mathcal F}^T,\ x\in\mathcal X\}.$$
--   If $\mathcal A$ is compound linear on $\mathcal D$, then the **value-of-information process**
--   $$D_t=C_t-A_t=C_t(\nu_t)-A_t(\nu_t),\qquad t=0,\dots,T,$$
--   is a supermartingale under $P$ with respect to $(\mathcal F_t)$.
--
--   $D_0=C_0-A_0$ is the value of perfect information of the multi-stage problem, a multi-period deviation-type risk functional; the supermartingale property says that this risk decreases in the mean as time moves towards the horizon $T$.
--
--   **Formalization Note** Same conventions as Lemmas 5.1 and 5.2: time `Fin (T + 1)` with a one-point root stage, finite node types with measurable singletons, both maxima encoded by `IsGreatest` at nodes of positive probability, Mathlib's `Filtration` equal to $\sigma(\nu_t)$ and Mathlib's `Supermartingale`. The domain $\mathcal D$ makes the book's parenthetical "in particular if $\mathcal A$ is the expectation" an instance: the expectation is compound linear on the distributions with a finite mean (Example 2.13 with $U(v)=v$), and on a finite tree every law of $H(x,\xi)$ has finitely many values. It is not stated separately. Non-anticipative decisions are clairvoyant (by the tree property), so the domain hypothesis is stated for clairvoyant decisions only.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 224, Corollary 5.3

import Mathlib
import Definitions.Def_RiskFunctionals_ValueOfInfo_Compounding
import Definitions.Def_RiskFunctionals_ValueOfInfo_IsTreeProcess
import Definitions.Def_RiskFunctionals_ValueOfInfo_DecisionProblems

namespace RiskFunctionals.ValueOfInfo

open MeasureTheory ProbabilityTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 224,
Corollary 5.3. The setting (pp. 221–223): a tree process `ν_t`, `t = 0, …, T`, on finitely many nodes per
stage, whose root stage `N 0` is a single node (so `ℱ₀` is trivial); the standard filtration
`ℱ_t = σ(ν_t)`; scenarios `ξ_t = f_t(ν_t)`; a measurable profit function `H(x, ξ)` with decisions in
`𝒳`; and a version-independent acceptability functional `𝒜` with domain `𝒟`.
The laws `𝒜` is applied to lie in its domain `𝒟`: the law of `H(x, ξ)` under `P^{ν_t=v}` is in `𝒟`
for every feasible clairvoyant `x` and every node of positive probability.
`A t v` and `C t v` are the maxima `A_t(v) = max{𝒜_{P^{ν_t=v}}[H(x, ξ)] : x ◁ 𝓕, x ∈ 𝒳}` and
`C_t(v) = max{𝒜_{P^{ν_t=v}}[H(x, ξ)] : x ◁ 𝓕^T, x ∈ 𝒳}` at every node `v` of positive
probability. If `𝒜` is compound linear on `𝒟`, the value-of-information process
`D_t = C_t − A_t = C_t(ν_t) − A_t(ν_t)` is a supermartingale under `P`. -/
theorem value_of_information_supermartingale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℕ} {N : Fin (T + 1) → Type*} [∀ t, MeasurableSpace (N t)]
    [∀ t, MeasurableSingletonClass (N t)] [∀ t, Finite (N t)] [Unique (N 0)]
    (ν : (t : Fin (T + 1)) → Ω → N t) (hν : ∀ t, Measurable (ν t)) (htree : IsTreeProcess ν)
    (ℱ : Filtration (Fin (T + 1)) ‹MeasurableSpace Ω›)
    (hℱ : ∀ t, ℱ t = MeasurableSpace.comap (ν t) inferInstance)
    {Ξ : Type*} [MeasurableSpace Ξ] (f : (i : Fin T) → N i.succ → Ξ)
    {𝕏 : Type*} [MeasurableSpace 𝕏] [MeasurableSingletonClass 𝕏] (𝒳 : Set (Fin T → 𝕏))
    (H : (Fin T → 𝕏) → (Fin T → Ξ) → ℝ) (hH : Measurable (Function.uncurry H))
    (𝒜 : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ))
    (h𝒟 : ∀ t (v : N t) (x : Ω → Fin T → 𝕏), P (ν t ⁻¹' {v}) ≠ 0 → IsClairvoyantAdapted ν x →
      (∀ ω, x ω ∈ 𝒳) → (P[|ν t ⁻¹' {v}]).map (profit ν f H x) ∈ 𝒟)
    (A C : (t : Fin (T + 1)) → N t → ℝ)
    (hA : ∀ t (v : N t), P (ν t ⁻¹' {v}) ≠ 0 →
      IsGreatest (optimalityValues 𝒜 P ν f H 𝒳 t v) (A t v))
    (hC : ∀ t (v : N t), P (ν t ⁻¹' {v}) ≠ 0 →
      IsGreatest (clairvoyantValues 𝒜 P ν f H 𝒳 t v) (C t v))
    (hlin : CompoundLinear 𝒟 𝒜) :
    Supermartingale (fun t ω => C t (ν t ω) - A t (ν t ω)) ℱ P := by sorry

end RiskFunctionals.ValueOfInfo
