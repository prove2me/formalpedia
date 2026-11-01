-- Prove2me | Theorems.Thm_SupermodDRO_proposition_3
-- name    : SupermodDRO.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:28.695739+00:00
-- url     : https://prove2.me/theorems/60aa8c4e-f1fb-4c26-a43a-29fecd4e8d34
-- title:
--   Proposition 3, p.10 — value identity: the worst case over $\mathcal F^k$ is the chain of Algorithm 1 (corrected: Algorithm 1 masses on degenerate coordinates)
-- statement:
--   Fix a scenario with data $(\mu,\delta,\underline z,\overline z)$ satisfying the assumptions of p.7, with $n\ge1$, and a first-stage decision $x$ such that $z\mapsto g(x,z)$ is supermodular and $>-\infty$. Then
--   $$
--   \sup_{\mathbb P\in\mathcal F^k}\mathbb E_{\mathbb P}[g(x,\tilde z)]=\sum_{i\in[2n+1]}p_i\,g(x,z^i),
--   $$
--   where $z^1,\dots,z^{2n+1}$ and $p$ are the output of Algorithm 1. Both sides lie in $(-\infty,+\infty]$.
--
--   So the worst case over a fixed scenario is a distribution on a chain of $2n+1$ points that does not depend on $x$.
--
--   **Formalization Note** Supermodularity of the extended-valued $g(x,\cdot)$ is the inequality of Definition 1 in $[-\infty,+\infty]$. Products are taken with $0\cdot\infty=0$. The clause "whose time complexity is $O(n)$" is not formalized.
--
--   Differences from the source:
--   - correction: Algorithm 1 reads the masses 1, 1, 1 of p.8 for a coordinate with z̲ᵢᵏ = z̄ᵢᵏ → masses (1, 0, 0) on the levels lower, mean, upper; reason: with the printed masses the weights sum to 3 and Theorem 1 fails: n = K = 1, δ = 0, g ≡ 1 give value 1 for (2) and 3 for (6), with every assumption of the paper satisfied
--   - reading: Definition 1 (supermodular) is for f : ℜⁿ → ℜ and is applied to g, which takes the value ∞ → the same inequality for the EReal-valued g(x, ·); reason: g(x, z) = ∞ when (1) is infeasible (p.6) and the paper applies Definition 1 to g
--   - generalization: standing assumption that Problem (2) has a finite optimal value → only its consequence g(x, ·) > −∞ is assumed; reason: the standing assumption implies g > −∞ everywhere, so the paper's setting is an instance
--   - reading: z̲ᵏ ≤ µᵏ ≤ z̄ᵏ and δᵏ ≥ 0 are never stated → assumed (in ScenarioAssumptions); reason: used throughout the paper: the support contains the mean, (5) is a probability vector, and p.7 treats µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ} as the boundary case
--   - encoding: n unrestricted → 0 < n; reason: Algorithm 1 takes a minimum over [n] and is undefined for n = 0; no instance where it is defined is excluded
--   - encoding: Algorithm 1 tracks the values of the coordinates → Algorithm 1 tracks their levels lower, mean, upper; reason: identical on coordinates with z̲ᵢ < µᵢ < z̄ᵢ; on z̲ᵢ = z̄ᵢ all levels have the same value
--   - encoding: expectation of the [−∞, ∞]-valued g → extended expectation ∫g⁺ − ∫g⁻ in EReal, +∞ when ∫g⁺ = ∞; reason: the standard convention; it agrees with the paper whenever the expectation is defined
--   - encoding: [K], [n], [2n+1] indexed from 1 → Fin K, Fin n, Fin (2n+1) indexed from 0; reason: Lean convention; same instances
--   - reading: Algorithm 1 whose time complexity is O(n) → the O(n) iteration count of the while loop, built into algorithm1 (exactly 2n iterations, 2n + 1 outputs); no running time is stated; reason: the clause does not fix a cost model and the platform has none; the iteration count is the reading that holds of the printed loop, since at unit cost per arithmetic operation each iteration takes a minimum over n entries
--   - encoding: g(x, z) = min b⊤y, with g(x, z) = ∞ if (1) is infeasible → the infimum in EReal: ⊤ on an empty feasible set, ⊥ on an unbounded program; reason: same value whenever (1) is infeasible or has an optimal value; the paper never writes the unbounded case
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proposition 3, p.10, with Algorithm 1, p.10

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Supermodular
import Definitions.Def_SupermodDRO_secondStageCost
import Definitions.Def_SupermodDRO_scenarioWorstCase
import Definitions.Def_SupermodDRO_ScenarioAssumptions
import Definitions.Def_SupermodDRO_algorithm1

namespace SupermodDRO

/-- **Proposition 3 (the worst case over `𝓕ᵏ` is Algorithm 1's chain).** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Proposition 3, p.10: "For any x, if g(x, z) is supermodular in z, we have sup_{ℙᵏ∈𝓕ᵏ} E[g(x, z̃)] =
Σ_{i∈[2n+1]} pᵢ g(x, zⁱ). Here p, zⁱ, i ∈ [2n + 1] are output by Algorithm 1 whose time complexity
is O(n)."

For one scenario with data satisfying the assumptions of p.7, `n ≥ 1`, and every `x` such that
`z ↦ g(x, z)` is supermodular and `> −∞`:
`sup_{P∈𝓕ᵏ} E_P[g(x, z̃)] = Σ_{i∈[2n+1]} pᵢ g(x, zⁱ)` in `[−∞, ∞]`, with `(z¹, …, z^{2n+1}; p)` the
output of Algorithm 1.

**Formalization Note** Supermodularity of the extended-real `g(x, ·)` is Definition 1 read in
`EReal` (the published `MDPFinance.StructuredModels.SupermodularOn` on the whole space). The
hypothesis `g(x, ·) > −∞` follows from the paper's standing assumption that Problem (2) has a finite
value. Algorithm 1 uses the masses `(1, 0, 0)` on coordinates with `z̲ᵢ = z̄ᵢ` (a correction). The
products are in `EReal` with `0 · ∞ = 0`. The clause "whose time complexity is O(n)" is read as the
iteration count of the `while` loop: `algorithm1State` runs exactly `2n` iterations and returns
`2n + 1` points and weights. No running time is stated: the platform has no cost model, and at unit
cost per arithmetic operation the printed loop (a minimum over `n` entries in each iteration) is not
linear in `n`. This item is the value identity of Proposition 3. -/
theorem proposition_3 {l m r n : ℕ} (W : Matrix (Fin r) (Fin l) ℝ) (U : Matrix (Fin r) (Fin m) ℝ)
    (V : Matrix (Fin r) (Fin n) ℝ) (v0 : Fin r → ℝ) (b : Fin m → ℝ) (μ δ zl zu : Fin n → ℝ)
    (hsc : ScenarioAssumptions μ δ zl zu) (hn : 0 < n) (x : Fin l → ℝ)
    (hsm : MDPFinance.StructuredModels.SupermodularOn Set.univ (secondStageCost W U V v0 b x))
    (hbot : ∀ z, secondStageCost W U V v0 b x z ≠ ⊥) :
    scenarioWorstCase (secondStageCost W U V v0 b x) μ δ zl zu =
      ∑ i, ((algorithm1Weight μ δ zl zu i : ℝ) : EReal) *
        secondStageCost W U V v0 b x (algorithm1Point μ δ zl zu i) := by sorry

end SupermodDRO
