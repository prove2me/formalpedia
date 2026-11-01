-- Prove2me | Theorems.Thm_SupermodDRO_finite_on_boxes
-- name    : SupermodDRO.finite_on_boxes
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:57.28126+00:00
-- url     : https://prove2.me/theorems/b768b7aa-74f9-43f0-a47c-3f5cbdd347e8
-- title:
--   Proof of Theorem 1, p.48 — on $\mathcal X_{fea}$ every scenario's worst case is finite and $g(x,\cdot)$ is finite on every box
-- statement:
--   Under the standing assumptions of §2, let $x\in\mathcal X$ with $\sup_{\mathbb P\in\mathcal F}\mathbb E_{\mathbb P}[g(x,\tilde z)]<\infty$ (that is, $x\in\mathcal X_{fea}$). Then for every scenario $k$
--   $$
--   -\infty<\sup_{\mathbb P^k\in\mathcal F^k}\mathbb E_{\mathbb P^k}[g(x,\tilde z)]<\infty,
--   $$
--   and $g(x,z)$ is finite for every $z\in[\underline z^k,\overline z^k]$.
--
--   This is what makes every constraint $Wx+Uy^{k,i}\ge Vz^{k,i}+v^0$ of (6) feasible at such $x$, including those of support points with weight $0$.
--
--   **Formalization Note** Supermodularity is not needed and not assumed.
--
--   Differences from the source:
--   - generalization: the proof of Theorem 1 assumes g(x, z) supermodular in z for any x → no supermodularity hypothesis; reason: this step uses only the scenario decomposition and the assumption on 𝒬; the paper's setting is an instance
--   - reading: z̲ᵏ ≤ µᵏ ≤ z̄ᵏ and δᵏ ≥ 0 are never stated → assumed (in ScenarioAssumptions); reason: used throughout the paper: the support contains the mean, (5) is a probability vector, and p.7 treats µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ} as the boundary case
--   - encoding: n unrestricted → 0 < n; reason: Algorithm 1 takes a minimum over [n] and is undefined for n = 0; no instance where it is defined is excluded
--   - encoding: expectation of the [−∞, ∞]-valued g → extended expectation ∫g⁺ − ∫g⁻ in EReal, +∞ when ∫g⁺ = ∞; reason: the standard convention; it agrees with the paper whenever the expectation is defined
--   - encoding: 𝓕 of (3) with constraints conditional on k̃ = k → joint laws of (k̃, z̃) with the conditional constraints multiplied by q_k; reason: identical for q_k > 0; for q_k = 0 the paper's conditioning is undefined and the constraints are void
--   - encoding: [K], [n], [2n+1] indexed from 1 → Fin K, Fin n, Fin (2n+1) indexed from 0; reason: Lean convention; same instances
--   - encoding: g(x, z) = min b⊤y, with g(x, z) = ∞ if (1) is infeasible → the infimum in EReal: ⊤ on an empty feasible set, ⊥ on an unbounded program; reason: same value whenever (1) is infeasible or has an optimal value; the paper never writes the unbounded case
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proof of Theorem 1 (App. C.4), p.48

import Mathlib
import Definitions.Def_SupermodDRO_Assumptions
import Definitions.Def_SupermodDRO_worstCaseCost
import Definitions.Def_SupermodDRO_scenarioWorstCase

namespace SupermodDRO

/-- **On `𝒳_fea` every scenario's worst case is finite and `g(x, ·)` is finite on every box.**
Long, Qi & Zhang, *Supermodularity in Two-Stage Distributionally Robust Optimization*, author
manuscript (June 2022), Proof of Theorem 1 (App. C.4), p.48: "Hence, for all k ∈ [K],
sup_{ℙᵏ∈𝓕ᵏ} E_{ℙᵏ}[g(x, z̃)] must be finite. It implies that g(x, z) is finite for all
z ∈ [z̲ᵏ, z̄ᵏ]."

Under the standing assumptions, for `x ∈ 𝒳` with `sup_{ℙ∈𝓕} E_ℙ[g(x, z̃)] < ∞` (that is,
`x ∈ 𝒳_fea`): for every scenario `k`, `sup_{ℙᵏ∈𝓕ᵏ} E_{ℙᵏ}[g(x, z̃)]` is finite, and `g(x, z)` is
finite for every `z ∈ [z̲ᵏ, z̄ᵏ]`.

**Formalization Note** "Finite" is `≠ ∞` and `≠ −∞` in `EReal`. The paper is inside the proof of
Theorem 1, whose hypothesis is that `g(x, z)` is supermodular in `z`; this step does not use it, and
it is not assumed here. -/
theorem finite_on_boxes {l m r n K s : ℕ} (D : Data l m r n K s) (hA : Assumptions D)
    (x : Fin l → ℝ) (hx : x ∈ D.X) (hwc : worstCaseCost D x < ⊤) :
    (∀ k, scenarioWorstCase (D.g x) (D.μ k) (D.δ k) (D.zl k) (D.zu k) ≠ ⊤ ∧
        scenarioWorstCase (D.g x) (D.μ k) (D.δ k) (D.zl k) (D.zu k) ≠ ⊥) ∧
      ∀ k, ∀ z ∈ Set.Icc (D.zl k) (D.zu k), D.g x z ≠ ⊤ ∧ D.g x z ≠ ⊥ := by sorry

end SupermodDRO
