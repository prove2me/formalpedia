-- Prove2me | Theorems.Thm_SupermodDRO_infinite_case
-- name    : SupermodDRO.infinite_case
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:30.327516+00:00
-- url     : https://prove2.me/theorems/c013c56b-6d45-4d7f-aaee-ccc8a74dea9d
-- title:
--   Proof of Theorem 1, p.48 — off $\mathcal X_{fea}$ some support point of Algorithm 1 is infeasible and $f(x)=\infty$ (corrected: Algorithm 1 masses on degenerate coordinates)
-- statement:
--   Under the standing assumptions of §2, let $x\in\mathcal X$ be such that $z\mapsto g(x,z)$ is supermodular and
--   $$
--   \sup_{\mathbb P\in\mathcal F}\mathbb E_{\mathbb P}[g(x,\tilde z)]=\infty
--   $$
--   (that is, $x\in\mathcal X\setminus\mathcal X_{fea}$). Then some support point $z^{k,i}$ returned by Algorithm 1 has $g(x,z^{k,i})=\infty$, and consequently the value $f(x)$ of the linear program (6) at $x$ is $\infty$.
--
--   So (6) is infeasible at exactly the first-stage decisions with infinite worst-case cost.
--
--   Differences from the source:
--   - correction: Algorithm 1 reads the masses 1, 1, 1 of p.8 for a coordinate with z̲ᵢᵏ = z̄ᵢᵏ → masses (1, 0, 0) on the levels lower, mean, upper; reason: with the printed masses the weights sum to 3 and Theorem 1 fails: n = K = 1, δ = 0, g ≡ 1 give value 1 for (2) and 3 for (6), with every assumption of the paper satisfied
--   - reading: Definition 1 (supermodular) is for f : ℜⁿ → ℜ and is applied to g, which takes the value ∞ → the same inequality for the EReal-valued g(x, ·); reason: g(x, z) = ∞ when (1) is infeasible (p.6) and the paper applies Definition 1 to g
--   - generalization: g(x, z) supermodular in z for any x → supermodular at the given x only; reason: the argument uses Proposition 3 at this x only; the paper's hypothesis implies this one
--   - reading: z̲ᵏ ≤ µᵏ ≤ z̄ᵏ and δᵏ ≥ 0 are never stated → assumed (in ScenarioAssumptions); reason: used throughout the paper: the support contains the mean, (5) is a probability vector, and p.7 treats µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ} as the boundary case
--   - encoding: n unrestricted → 0 < n; reason: Algorithm 1 takes a minimum over [n] and is undefined for n = 0; no instance where it is defined is excluded
--   - encoding: Algorithm 1 tracks the values of the coordinates → Algorithm 1 tracks their levels lower, mean, upper; reason: identical on coordinates with z̲ᵢ < µᵢ < z̄ᵢ; on z̲ᵢ = z̄ᵢ all levels have the same value
--   - encoding: expectation of the [−∞, ∞]-valued g → extended expectation ∫g⁺ − ∫g⁻ in EReal, +∞ when ∫g⁺ = ∞; reason: the standard convention; it agrees with the paper whenever the expectation is defined
--   - encoding: 𝓕 of (3) with constraints conditional on k̃ = k → joint laws of (k̃, z̃) with the conditional constraints multiplied by q_k; reason: identical for q_k > 0; for q_k = 0 the paper's conditioning is undefined and the constraints are void
--   - encoding: [K], [n], [2n+1] indexed from 1 → Fin K, Fin n, Fin (2n+1) indexed from 0; reason: Lean convention; same instances
--   - encoding: g(x, z) = min b⊤y, with g(x, z) = ∞ if (1) is infeasible → the infimum in EReal: ⊤ on an empty feasible set, ⊥ on an unbounded program; reason: same value whenever (1) is infeasible or has an optimal value; the paper never writes the unbounded case
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proof of Theorem 1 (App. C.4), p.48

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Supermodular
import Definitions.Def_SupermodDRO_Assumptions
import Definitions.Def_SupermodDRO_worstCaseCost
import Definitions.Def_SupermodDRO_lpFeasible

namespace SupermodDRO

/-- **Off `𝒳_fea` some support point of Algorithm 1 is infeasible, so `f(x) = ∞`.** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Proof of Theorem 1 (App. C.4), p.48: "Since any feasible q ∈ 𝒬 ⊆ {q ∈ ℜᴷ₊ | Σ_{k∈[K]} q_k = 1} is
bounded, there must be k ∈ [K] such that ∞ = sup_{ℙᵏ∈𝓕ᵏ} E_{ℙᵏ}[g(x, z̃)] = Σ_{i∈[2n+1]} pᵢᵏ
g(x, z^{k,i}), where the last equality follows from Proposition 3. Again, since pᵢᵏ ∈ [0, 1] for all
i ∈ [2n + 1], there exists a specific i ∈ [2n + 1] such that g(x, z^{k,i}) = ∞. … Hence, f(x) = ∞."

Under the standing assumptions, for `x ∈ 𝒳` with `g(x, ·)` supermodular and
`sup_{ℙ∈𝓕} E_ℙ[g(x, z̃)] = ∞` (that is, `x ∈ 𝒳 ∖ 𝒳_fea`, p.48): some support point `z^{k,i}` of
Algorithm 1 has `g(x, z^{k,i}) = ∞`, and the value `f(x)` of (6) at `x` is `∞`.

**Formalization Note** Supermodularity is assumed at this `x` only (the paper assumes it for every
`x`); the argument uses Proposition 3 at this `x`. Values in `EReal`; Algorithm 1 with the corrected
masses on coordinates with `z̲ᵢᵏ = z̄ᵢᵏ`. -/
theorem infinite_case {l m r n K s : ℕ} (D : Data l m r n K s) (hA : Assumptions D)
    (x : Fin l → ℝ) (hx : x ∈ D.X)
    (hsm : MDPFinance.StructuredModels.SupermodularOn Set.univ (D.g x))
    (hwc : worstCaseCost D x = ⊤) :
    (∃ k i, D.g x (algorithm1Point (D.μ k) (D.δ k) (D.zl k) (D.zu k) i) = ⊤) ∧
      lpInnerValue D x = ⊤ := by sorry

end SupermodDRO
