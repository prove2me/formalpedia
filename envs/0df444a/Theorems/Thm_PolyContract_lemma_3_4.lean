-- Prove2me | Theorems.Thm_PolyContract_lemma_3_4
-- name    : PolyContract.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:49:11.360208+00:00
-- url     : https://prove2.me/theorems/029a367a-524f-4c97-87e9-95b57dc95d42
-- title:
--   Lemma 3.4 — the best response is continuous and piecewise affine
-- statement:
--   Let $(f,m,\beta)$ be a valid instance with quadratic costs. The map $\alpha\mapsto x^\star(\alpha)$ is continuous and piecewise affine on $[0,\infty)$ with finitely many breakpoints. Indeed, $x^\star(\alpha)$ is the projection of $z(\alpha)=\alpha t$ onto $P^{(+)}(f)$ in the inner product $u^\top\mathrm{diag}(\beta)v$, i.e. the minimizer over $P^{(+)}(f)$ of
--   $$\sum_e\beta_e(x_e-\alpha t_e)^2.$$
--
--   On each piece the principal's utility is a quadratic polynomial, so an optimal contract is found among finitely many candidates.
--
--   Differences from the source:
--   - reading: piecewise affine on [0, ∞) with finitely many breakpoints; x⋆(α) is the projection of αt → a choice of best responses that is continuous on [0, ∞) and affine on [a_i, a_{i+1}] and [a_K, ∞) for some 0 = a_0 < ⋯ < a_K; the best responses are exactly the minimizers of Σ β_e(x_e − α t_e)² over P(+)(f); reason: the standard meaning of the terms; the best response is unique (§3, p.7)
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Lemma 3.4, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract

/-- **Lemma 3.4** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.8). "The map `α ↦ x⋆(α)` is continuous and piecewise affine on `[0, ∞)` with
finitely many breakpoints. Indeed, `x⋆(α)` is the projection of `z(α)` onto `P(+)(f)` in the inner
product `u⊤diag(β)v`," where `z(α) = αt` (3.1).

**Formalization Note** Valid instance with quadratic costs. `x⋆` is a function choosing a best
response at every `α ≥ 0`. "Piecewise affine with finitely many breakpoints" reads: there are
`0 = a₀ < a₁ < ⋯ < a_K` such that `x⋆` is affine on each `[a_i, a_{i+1}]` and on `[a_K, ∞)`.
"The projection of `αt` onto `P(+)(f)` in `u⊤diag(β)v`" reads: `x` minimizes
`Σ_e β_e (x_e − α t_e)²` over `P(+)(f)`; the clause says that the best responses are exactly
these minimizers. -/
theorem lemma_3_4 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (I : QuadInstance ι) (hI : I.Valid) :
    ∃ xs : ℝ → ι → ℝ, (∀ α : ℝ, 0 ≤ α → I.IsBestResponse α (xs α)) ∧
      ContinuousOn xs (Set.Ici 0) ∧
      (∃ (K : ℕ) (a : Fin (K + 1) → ℝ), a 0 = 0 ∧ StrictMono a ∧
        (∀ i : Fin K, ∃ u v : ι → ℝ, ∀ α ∈ Set.Icc (a i.castSucc) (a i.succ), xs α = u + α • v) ∧
        ∃ u v : ι → ℝ, ∀ α : ℝ, a (Fin.last K) ≤ α → xs α = u + α • v) ∧
      ∀ α : ℝ, 0 ≤ α → ∀ x : ι → ℝ, I.IsBestResponse α x ↔
        (x ∈ indepPoly I.f ∧ ∀ y ∈ indepPoly I.f,
          ∑ e, I.β e * (x e - α * I.t e) ^ 2 ≤ ∑ e, I.β e * (y e - α * I.t e) ^ 2) := by sorry

end PolyContract
