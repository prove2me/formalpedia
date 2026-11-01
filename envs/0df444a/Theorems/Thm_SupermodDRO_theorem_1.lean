-- Prove2me | Theorems.Thm_SupermodDRO_theorem_1
-- name    : SupermodDRO.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:45.310655+00:00
-- url     : https://prove2.me/theorems/11cfd9b3-0319-4d8a-b2c7-6bc7b5ec2521
-- title:
--   Theorem 1, p.12 — Problem (2) is equivalent to the linear program (6) (corrected: Algorithm 1 masses on degenerate coordinates)
-- statement:
--   Consider the two-stage distributionally robust problem
--   $$
--   \min_{x\in\mathcal X}\Bigl\{a^\top x+\sup_{\mathbb P\in\mathcal F}\mathbb E_{\mathbb P}[g(x,\tilde z)]\Bigr\}\tag{2}
--   $$
--   with the second-stage cost (1) and the scenario-wise ambiguity set (3), under the standing assumptions of §2: (2) has a finite optimal value, $\mathcal Q$ lies in the probability simplex, every scenario has positive probability for some $q\in\mathcal Q$, the data of every scenario satisfy the assumptions of p.7, and $n\ge1$. Let $z^{k,1},\dots,z^{k,2n+1},p^k$ be the output of Algorithm 1 for scenario $k$, and consider the linear program
--   $$
--   \begin{aligned}
--   \min\ & a^\top x+\nu^\top l\\
--   \text{s.t. }& R_k^\top l\ge\sum_{i\in[2n+1]}p_i^k\,b^\top y^{k,i}, && k\in[K],\\
--   & Wx+Uy^{k,i}\ge Vz^{k,i}+v^0, && k\in[K],\ i\in[2n+1],\\
--   & l\ge0,\ x\in\mathcal X.
--   \end{aligned}\tag{6}
--   $$
--   If $z\mapsto g(x,z)$ is supermodular for every $x\in\mathcal X$, then (2) is equivalent to (6):
--
--   1. for every $x\in\mathcal X$, $\sup_{\mathbb P\in\mathcal F}\mathbb E_{\mathbb P}[g(x,\tilde z)]=f(x)$, the optimal value of (6) in $(l,y)$ at $x$ (both may be $+\infty$);
--   2. (2) and (6) have the same optimal value;
--   3. $x^*\in\mathcal X$ is optimal for (2) if and only if there are $l,y$ such that $(x^*,l,y)$ is feasible and optimal for (6).
--
--   The reformulation has $K(2n+1)$ copies of the second-stage variables, polynomially many, and needs no relatively complete recourse.
--
--   **Formalization Note** Values are in $[-\infty,+\infty]$; "min" is the infimum. The expectation is the extended one. Algorithm 1 uses the masses $(1,0,0)$ on coordinates with $\underline z_i^k=\overline z_i^k$.
--
--   Differences from the source:
--   - correction: Algorithm 1 reads the masses 1, 1, 1 of p.8 for a coordinate with z̲ᵢᵏ = z̄ᵢᵏ → masses (1, 0, 0) on the levels lower, mean, upper; reason: with the printed masses the weights sum to 3 and Theorem 1 fails: n = K = 1, δ = 0, g ≡ 1 give value 1 for (2) and 3 for (6), with every assumption of the paper satisfied
--   - reading: Definition 1 (supermodular) is for f : ℜⁿ → ℜ and is applied to g, which takes the value ∞ → the same inequality for the EReal-valued g(x, ·); reason: g(x, z) = ∞ when (1) is infeasible (p.6) and the paper applies Definition 1 to g
--   - reading: z̲ᵏ ≤ µᵏ ≤ z̄ᵏ and δᵏ ≥ 0 are never stated → assumed (in ScenarioAssumptions); reason: used throughout the paper: the support contains the mean, (5) is a probability vector, and p.7 treats µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ} as the boundary case
--   - generalization: g(x, z) supermodular in z for any x → supermodular for every x ∈ 𝒳; reason: the proof uses supermodularity only at points of 𝒳; the paper's hypothesis implies this one
--   - encoding: expectation of the [−∞, ∞]-valued g → extended expectation ∫g⁺ − ∫g⁻ in EReal, +∞ when ∫g⁺ = ∞; reason: the standard convention; it agrees with the paper whenever the expectation is defined
--   - encoding: 𝓕 of (3) with constraints conditional on k̃ = k → joint laws of (k̃, z̃) with the conditional constraints multiplied by q_k; reason: identical for q_k > 0; for q_k = 0 the paper's conditioning is undefined and the constraints are void
--   - encoding: Algorithm 1 tracks the values of the coordinates → Algorithm 1 tracks their levels lower, mean, upper; reason: identical on coordinates with z̲ᵢ < µᵢ < z̄ᵢ; on z̲ᵢ = z̄ᵢ all levels have the same value
--   - encoding: n unrestricted → 0 < n; reason: Algorithm 1 takes a minimum over [n] and is undefined for n = 0; no instance where it is defined is excluded
--   - encoding: [K], [n], [2n+1] indexed from 1 → Fin K, Fin n, Fin (2n+1) indexed from 0; reason: Lean convention; same instances
--   - encoding: Problem (2) is equivalent to the linear program (6), both written with min → (a) worst-case cost = f(x) for every x ∈ 𝒳, (b) equal optimal values, (c) the same optimal x; min read as infimum in EReal; reason: the proof establishes (a) and the paper uses optimal solutions of (6) as optimal for (2); attainment is not assumed
--   - encoding: g(x, z) = min b⊤y, with g(x, z) = ∞ if (1) is infeasible → the infimum in EReal: ⊤ on an empty feasible set, ⊥ on an unbounded program; reason: same value whenever (1) is infeasible or has an optimal value; the paper never writes the unbounded case
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Theorem 1 and (6), p.12; proof pp.47–48

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Supermodular
import Definitions.Def_SupermodDRO_Assumptions
import Definitions.Def_SupermodDRO_worstCaseCost
import Definitions.Def_SupermodDRO_problem2Value
import Definitions.Def_SupermodDRO_lpFeasible

open Matrix

namespace SupermodDRO

/-- **Theorem 1 (Problem (2) is equivalent to the linear program (6)).** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Theorem 1, p.12: "If g(x, z) is supermodular in z for any x, Problem (2) is equivalent to the
following linear program, min a⊤x + ν⊤l s.t. R_k⊤l ≥ Σ_{i∈[2n+1]} pᵢᵏ b⊤y^{k,i}, k ∈ [K];
Wx + Uy^{k,i} ≥ Vz^{k,i} + v⁰, k ∈ [K], i ∈ [2n + 1]; l ≥ 0, x ∈ 𝒳. (6)", where
"z^{k,1}, …, z^{k,2n+1}, pᵏ [is] the output of Algorithm 1 with input 𝓕ᵏ for all k ∈ [K]" (p.12).

Under the standing assumptions of §2 (`Assumptions`), if `z ↦ g(x, z)` is supermodular for every
`x ∈ 𝒳`, then:
1. for every `x ∈ 𝒳`, `sup_{ℙ∈𝓕} E_ℙ[g(x, z̃)] = f(x)`, the optimal value of (6) in `(l, y)` at `x`
   (both may be `∞`);
2. Problem (2) and the linear program (6) have the same optimal value;
3. `x* ∈ 𝒳` is optimal for (2) if and only if there are `l, y` such that `(x*, l, y)` is feasible
   and optimal for (6).

**Formalization Note** "Equivalent" is read as items 1–3 (the proof establishes 1, p.48, and the
paper uses optimal solutions of (6) as optimal for (2)); "min" is the infimum in `EReal`. The worst
case is over joint laws of `(k̃, z̃)` with the conditional constraints multiplied by `q_k`, and the
expectation is the extended one (`DupacovaWets.Consistency.expect`). Supermodularity of the
extended-real `g(x, ·)` is Definition 1 read in `EReal`, assumed for `x ∈ 𝒳` (the paper says "for
any x"). Algorithm 1 uses the masses `(1, 0, 0)` on coordinates with `z̲ᵢᵏ = z̄ᵢᵏ`: with the printed
masses `(1, 1, 1)` the theorem is false. Indices are 0-based. -/
theorem theorem_1 {l m r n K s : ℕ} (D : Data l m r n K s) (hA : Assumptions D)
    (hsm : ∀ x ∈ D.X, MDPFinance.StructuredModels.SupermodularOn Set.univ (D.g x)) :
    (∀ x ∈ D.X, worstCaseCost D x = lpInnerValue D x) ∧
      problem2Value D = lpValue D ∧
      ∀ x ∈ D.X, (((D.a ⬝ᵥ x : ℝ) : EReal) + worstCaseCost D x = problem2Value D ↔
        ∃ (lv : Fin s → ℝ) (y : Fin K → Fin (2 * n + 1) → Fin m → ℝ),
          lpFeasible D x lv y ∧ ((D.a ⬝ᵥ x + D.ν ⬝ᵥ lv : ℝ) : EReal) = lpValue D) := by sorry

end SupermodDRO
