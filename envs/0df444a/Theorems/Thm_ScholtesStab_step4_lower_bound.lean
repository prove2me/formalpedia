-- Prove2me | Theorems.Thm_ScholtesStab_step4_lower_bound
-- name    : ScholtesStab.step4_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:14.164271+00:00
-- url     : https://prove2.me/theorems/c3d91834-56ca-40e9-a57c-fcd4ffec2e12
-- title:
--   Proof of Theorem 1, Step 4: the lower bound of (11)
-- statement:
--   Let $t_k>0$ with $t_k\to0$, and let $x^k\in M^{\mathcal S}$ be nondegenerate Karush–Kuhn–Tucker points of $\mathcal S$ with parameter $t_k$, all of the same quadratic index $q$, converging to $\bar x$. Suppose $\bar x\in M$ is a nondegenerate C-stationary point of MPCC (NDC1–NDC3) with multipliers $(\bar\sigma,\bar\varrho)$, and let $CI$ be its C-index.
--   Then
--
--   $$
--   \max\bigl\{q-|\{j\in a_{01}(\bar x)\mid\bar\sigma_{1,j}=0\}|-|\{j\in a_{10}(\bar x)\mid\bar\sigma_{2,j}=0\}|,\ 0\bigr\}\ \le\ CI .
--   $$
--
--   This is the left inequality of (11): the C-index of the limit can drop below the quadratic index of the approximating points by at most the number of vanishing multipliers $\bar\sigma$.
--
--   Differences from the source:
--   - encoding: ℝⁿ, indices j = 1, …, κ → EuclideanSpace ℝ (Fin n), indices in Fin κ (0-based); reason: a relabelling of coordinates and indices; same instances
--   - encoding: f, F₁, F₂ twice continuously differentiable (standing assumption, p.1) → ContDiff ℝ 2 fields of the structure MPCC; reason: the standing assumption is carried by every instance; same instances
--   - encoding: differentials DF(x), Hessians D²L(x) → fderiv ℝ F x : ℝⁿ →L[ℝ] ℝ and fderiv ℝ (fderiv ℝ L) x as a bilinear form; reason: the Fréchet derivative of a C² function is its differential and its second derivative is the Hessian; linear independence of differentials is that of gradients
--   - encoding: multipliers σ̄₁,ⱼ (j ∈ a₀₁), σ̄₂,ⱼ (j ∈ a₁₀), ϱ̄₁,ⱼ, ϱ̄₂,ⱼ (j ∈ a₀₀) → total functions Fin κ → ℝ whose values outside these index sets are never used; reason: every formula and count ranges over the paper's index sets only; same instances
--   - encoding: a sequence xᵗ converging to x̄ for t → 0 ("for all sufficiently small t", "for infinitely many t") → t : ℕ → ℝ with t k > 0 and t k → 0, x k → x̄; ∀ᶠ k in atTop and ∃ᶠ k in atTop; reason: the standard sequential reading of the paper's sequence; t k > 0 because S is defined for t > 0
--   - encoding: nondegenerate KKT points xᵗ with (unique) multipliers (ηᵗ, νᵗ) and quadratic index q → ∀ k, ∃ μ, IsNondegKKT (t k) (x k) μ ∧ QIS (t k) (x k) μ = q; reason: the multipliers are unique under ND1, so 'some multipliers' and 'the multipliers' coincide
--   - encoding: number of negative eigenvalues of the restricted Hessian D²L↾𝒯 → negIndex: the largest dimension of a subspace of 𝒯 on which the Hessian form is negative definite; reason: by Sylvester's law of inertia the two numbers coincide for the symmetric Hessian, in any basis of 𝒯
--   - encoding: the restricted Hessian matrix D²L↾𝒯 is nonsingular → NonsingularOn: the only ξ ∈ 𝒯 with D²L(ξ, η) = 0 for all η ∈ 𝒯 is ξ = 0; reason: this is the trivial kernel of the matrix of D²L↾𝒯 in a basis of 𝒯
--   - encoding: max {q − |…| − |…|, 0} ≤ CI → the inequality computed in ℤ with natural-number casts; reason: avoids truncated subtraction; same numbers
--   - generalization: CI ≥ max {q − |{j ∈ a₀₁(x̄) | σ̄₁,ⱼ = 0}|, 0} under the proof's assumption a₁₀(x̄) = ∅ → the left inequality of (11) with the a₁₀ count, as stated in Theorem 1; reason: with a₁₀(x̄) = ∅ the a₁₀ count is 0 and the printed line results
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, Proof of Theorem 1, Step 4, p.20 (last display); left inequality of (11), p.9

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01
import Definitions.Def_ScholtesStab_MPCC_IsCStationary
import Definitions.Def_ScholtesStab_MPCC_IsNondegCStationary
import Definitions.Def_ScholtesStab_MPCC_a01neg
import Definitions.Def_ScholtesStab_MPCC_CI
import Definitions.Def_ScholtesStab_MPCC_IsKKT
import Definitions.Def_ScholtesStab_MPCC_IsNondegKKT

namespace ScholtesStab

open MPCC Filter Topology

/-- **The lower bound of (11).** Lämmel–Shikhman, arXiv:2501.07383v2, Proof of Theorem 1,
Step 4, p.20: "We thus obtain: CI ≥ max {q − |{j ∈ a₀₁(x̄) | σ̄₁,ⱼ = 0}|, 0}."

Setting (the hypotheses of Theorem 1, p.9): parameters `t k > 0` with `t k → 0`, points
`x k → x̄`, each `x k` a nondegenerate KKT point of S with parameter `t k` (for some multipliers
`(η, ν)`) whose quadratic index is `q` (the same `q` for every `k`), and `x̄ ∈ M` a nondegenerate
C-stationary point of MPCC with multipliers `(σ̄, ϱ̄)` (NDC1–NDC3).
Then, in `ℤ`,
`max {q − |{j ∈ a₀₁(x̄) | σ̄₁,ⱼ = 0}| − |{j ∈ a₁₀(x̄) | σ̄₂,ⱼ = 0}|, 0} ≤ CI`.

**Formalization Note.** The proof assumes `a₁₀(x̄) = ∅` without loss of generality, so the
printed line omits the `a₁₀` count; the statement is the left inequality of (11) as stated in
Theorem 1. The sequence `x k` encodes "xᵗ for t → 0"; the multipliers of each `x k` are
existentially quantified (they are unique by ND1). -/
theorem step4_lower_bound {n κ : ℕ} (P : MPCC n κ) (t : ℕ → ℝ) (x : ℕ → E n) (xbar : E n)
    (m : MPCCMult κ) (q : ℕ) (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0))
    (hx : Tendsto x atTop (𝓝 xbar))
    (hKKT : ∀ k, ∃ μ : SMult κ, P.IsNondegKKT (t k) (x k) μ ∧ P.QIS (t k) (x k) μ = q)
    (hbar : P.IsNondegCStationary xbar m) :
    max ((q : ℤ) - (P.a01zero xbar m).card - (P.a10zero xbar m).card) 0 ≤ (P.CI xbar m : ℤ) := by sorry

end ScholtesStab
