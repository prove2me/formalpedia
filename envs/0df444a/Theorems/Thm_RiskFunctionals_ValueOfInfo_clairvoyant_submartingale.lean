-- Prove2me | Theorems.Thm_RiskFunctionals_ValueOfInfo_clairvoyant_submartingale
-- name    : RiskFunctionals.ValueOfInfo.clairvoyant_submartingale
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:33.157987+00:00
-- url     : https://prove2.me/theorems/57303e05-1b14-4d7e-bf90-c7fa322b17eb
-- title:
--   Lemma 5.1 — the clairvoyant process is a submartingale (a martingale for compound linear 𝒜)
-- statement:
--   Let $(\nu_t)_{t=0,\dots,T}$ be a tree process on $(\Omega,\mathcal F,P)$ with finitely many nodes at each stage and a single root node at $t=0$, with standard filtration $\mathcal F_t=\sigma(\nu_t)$. Let $\xi_t=f_t(\nu_t)$ be the scenario variables, $H(x,\xi)$ a measurable profit function, $\mathcal X$ the decision space and $\mathcal A$ a version-independent acceptability functional with domain $\mathcal D$, which contains the law of $H(x,\xi)$ under $P^{\{\nu_t=v\}}$ for every feasible clairvoyant decision $x$ ($x\lhd\boldsymbol{\mathcal F}^T$, $x\in\mathcal X$) and every node $v$ with $P\{\nu_t=v\}>0$. For every stage $t$ and every node $v$ with $P\{\nu_t=v\}>0$ suppose the clairvoyant's conditional problem attains its maximum
--   $$C_t(v)=\max\{\mathcal A_{P^{\{\nu_t=v\}}}[H(x,\xi)] : x\lhd\boldsymbol{\mathcal F}^T,\ x\in\mathcal X\},$$
--   and let $C_t=C_t(\nu_t)$ be the **clairvoyant process**. Then
--
--   1. if $\mathcal A$ is compound convex on $\mathcal D$, $(C_t)$ is a submartingale under $P$ with respect to $(\mathcal F_t)$;
--   2. if $\mathcal A$ is compound linear on $\mathcal D$, $(C_t)$ is a martingale under $P$ with respect to $(\mathcal F_t)$.
--
--   The clairvoyant knows the whole scenario from the start; the lemma says that, measured by a compound linear functional, the clairvoyant's conditional optimal value evolves as a fair game along the tree.
--
--   **Formalization Note** Time is `Fin (T + 1)`; the root stage $\mathcal N_0$ is a one-point type, so $\mathcal F_0$ is trivial and $C_0$ is the clairvoyant's problem (5.17). Nodes are finite types with measurable singletons; this is the setting in which every conditional probability $P^{\{\nu_t=v\}}$ of a positive-probability node is defined and every process is integrable. The maximum is encoded by the hypothesis that `C t v` is the greatest element of the set of clairvoyant values, required only at nodes of positive probability (the values at null nodes do not affect the process almost surely). The filtration is a Mathlib `Filtration` equal to $\sigma(\nu_t)$ at each stage; (sub)martingale is Mathlib's notion (adapted, integrable, conditional-expectation inequality). The decision space carries measurable singletons, so that measurability with respect to $\sigma(\nu_t)$ means that the decision is a function of the node.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 223, Lemma 5.1

import Mathlib
import Definitions.Def_RiskFunctionals_ValueOfInfo_Compounding
import Definitions.Def_RiskFunctionals_ValueOfInfo_IsTreeProcess
import Definitions.Def_RiskFunctionals_ValueOfInfo_DecisionProblems

namespace RiskFunctionals.ValueOfInfo

open MeasureTheory ProbabilityTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 223,
Lemma 5.1. The setting (pp. 221–223): a tree process `ν_t`, `t = 0, …, T`, on finitely many nodes per
stage, whose root stage `N 0` is a single node (so `ℱ₀` is trivial); the standard filtration
`ℱ_t = σ(ν_t)`; scenarios `ξ_t = f_t(ν_t)`; a measurable profit function `H(x, ξ)` with decisions in
`𝒳`; and a version-independent acceptability functional `𝒜` with domain `𝒟`.
The laws `𝒜` is applied to lie in its domain `𝒟`: the law of `H(x, ξ)` under `P^{ν_t=v}` is in `𝒟`
for every feasible clairvoyant `x` and every node of positive probability.
`C t v` is the maximum `C_t(v) = max{𝒜_{P^{ν_t=v}}[H(x, ξ)] : x ◁ 𝓕^T, x ∈ 𝒳}` at every node
`v` of positive probability. (i) If `𝒜` is compound convex on `𝒟`, the clairvoyant process
`C_t = C_t(ν_t)` is a submartingale under `P`; (ii) if `𝒜` is compound linear on `𝒟`, it is a
martingale under `P`. -/
theorem clairvoyant_submartingale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (C : (t : Fin (T + 1)) → N t → ℝ)
    (hC : ∀ t (v : N t), P (ν t ⁻¹' {v}) ≠ 0 →
      IsGreatest (clairvoyantValues 𝒜 P ν f H 𝒳 t v) (C t v)) :
    (CompoundConvex 𝒟 𝒜 → Submartingale (fun t ω => C t (ν t ω)) ℱ P) ∧
    (CompoundLinear 𝒟 𝒜 → Martingale (fun t ω => C t (ν t ω)) ℱ P) := by sorry

end RiskFunctionals.ValueOfInfo
