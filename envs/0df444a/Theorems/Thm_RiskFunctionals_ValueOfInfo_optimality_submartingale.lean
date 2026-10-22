-- Prove2me | Theorems.Thm_RiskFunctionals_ValueOfInfo_optimality_submartingale
-- name    : RiskFunctionals.ValueOfInfo.optimality_submartingale
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:32.522206+00:00
-- url     : https://prove2.me/theorems/f2896117-7755-49a8-9a91-c0c8e72ff03d
-- title:
--   Lemma 5.2 — the optimality process is a submartingale
-- statement:
--   Let $(\nu_t)_{t=0,\dots,T}$ be a tree process on $(\Omega,\mathcal F,P)$ with finitely many nodes at each stage and a single root node at $t=0$, with standard filtration $\mathcal F_t=\sigma(\nu_t)$. Let $\xi_t=f_t(\nu_t)$ be the scenario variables, $H(x,\xi)$ a measurable profit function, $\mathcal X$ the decision space and $\mathcal A$ a version-independent acceptability functional with domain $\mathcal D$, which contains the law of $H(x,\xi)$ under $P^{\{\nu_t=v\}}$ for every feasible non-anticipative decision $x$ ($x\lhd\boldsymbol{\mathcal F}$, $x\in\mathcal X$) and every node $v$ with $P\{\nu_t=v\}>0$. For every stage $t$ and every node $v$ with $P\{\nu_t=v\}>0$ suppose the non-anticipative conditional problem attains its maximum
--   $$A_t(v)=\max\{\mathcal A_{P^{\{\nu_t=v\}}}[H(x,\xi)] : x\lhd\boldsymbol{\mathcal F},\ x\in\mathcal X\},$$
--   and let $A_t=A_t(\nu_t)$ be the **optimality process**. If $\mathcal A$ is compound convex on $\mathcal D$, then $(A_t)$ is a submartingale under $P$ with respect to $(\mathcal F_t)$.
--
--   The optimality process is the value of the multi-stage decision problem re-solved on each conditional subtree; $A_0$ is the multi-stage problem (5.16) itself.
--
--   **Formalization Note** Same conventions as Lemma 5.1: time `Fin (T + 1)` with a one-point root stage, finite node types with measurable singletons, the maximum encoded by `IsGreatest` at nodes of positive probability, Mathlib's `Filtration` equal to $\sigma(\nu_t)$ and Mathlib's `Submartingale`. Non-anticipativity requires $x_t$ to be $\sigma(\nu_t)$-measurable for $t=0,\dots,T-1$, so $x_0$ is deterministic; the decision space carries measurable singletons.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 224, Lemma 5.2

import Mathlib
import Definitions.Def_RiskFunctionals_ValueOfInfo_Compounding
import Definitions.Def_RiskFunctionals_ValueOfInfo_IsTreeProcess
import Definitions.Def_RiskFunctionals_ValueOfInfo_DecisionProblems

namespace RiskFunctionals.ValueOfInfo

open MeasureTheory ProbabilityTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 224,
Lemma 5.2. The setting (pp. 221–223): a tree process `ν_t`, `t = 0, …, T`, on finitely many nodes per
stage, whose root stage `N 0` is a single node (so `ℱ₀` is trivial); the standard filtration
`ℱ_t = σ(ν_t)`; scenarios `ξ_t = f_t(ν_t)`; a measurable profit function `H(x, ξ)` with decisions in
`𝒳`; and a version-independent acceptability functional `𝒜` with domain `𝒟`.
The laws `𝒜` is applied to lie in its domain `𝒟`: the law of `H(x, ξ)` under `P^{ν_t=v}` is in `𝒟`
for every feasible non-anticipative `x` and every node of positive probability.
`A t v` is the maximum `A_t(v) = max{𝒜_{P^{ν_t=v}}[H(x, ξ)] : x ◁ 𝓕, x ∈ 𝒳}` at every node
`v` of positive probability. If `𝒜` is compound convex on `𝒟`, the optimality process
`A_t = A_t(ν_t)` is a submartingale under `P`. -/
theorem optimality_submartingale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℕ} {N : Fin (T + 1) → Type*} [∀ t, MeasurableSpace (N t)]
    [∀ t, MeasurableSingletonClass (N t)] [∀ t, Finite (N t)] [Unique (N 0)]
    (ν : (t : Fin (T + 1)) → Ω → N t) (hν : ∀ t, Measurable (ν t)) (htree : IsTreeProcess ν)
    (ℱ : Filtration (Fin (T + 1)) ‹MeasurableSpace Ω›)
    (hℱ : ∀ t, ℱ t = MeasurableSpace.comap (ν t) inferInstance)
    {Ξ : Type*} [MeasurableSpace Ξ] (f : (i : Fin T) → N i.succ → Ξ)
    {𝕏 : Type*} [MeasurableSpace 𝕏] [MeasurableSingletonClass 𝕏] (𝒳 : Set (Fin T → 𝕏))
    (H : (Fin T → 𝕏) → (Fin T → Ξ) → ℝ) (hH : Measurable (Function.uncurry H))
    (𝒜 : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ))
    (h𝒟 : ∀ t (v : N t) (x : Ω → Fin T → 𝕏), P (ν t ⁻¹' {v}) ≠ 0 → IsNonanticipative ν x →
      (∀ ω, x ω ∈ 𝒳) → (P[|ν t ⁻¹' {v}]).map (profit ν f H x) ∈ 𝒟)
    (A : (t : Fin (T + 1)) → N t → ℝ)
    (hA : ∀ t (v : N t), P (ν t ⁻¹' {v}) ≠ 0 →
      IsGreatest (optimalityValues 𝒜 P ν f H 𝒳 t v) (A t v))
    (hconv : CompoundConvex 𝒟 𝒜) :
    Submartingale (fun t ω => A t (ν t ω)) ℱ P := by sorry

end RiskFunctionals.ValueOfInfo
