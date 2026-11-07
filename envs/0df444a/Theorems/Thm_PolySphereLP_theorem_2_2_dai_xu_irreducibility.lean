-- Prove2me | Theorems.Thm_PolySphereLP_theorem_2_2_dai_xu_irreducibility
-- name    : PolySphereLP.theorem_2_2_dai_xu_irreducibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:39.743838+00:00
-- url     : https://prove2.me/theorems/a7fa59c1-0ef1-4dd3-bccd-4ca21f01ddfb
-- title:
--   Theorem 2.2 — Dai–Xu irreducibility of $\mathcal H^{\mathbb C}_{n,k}$
-- statement:
--   Let $n\ge3$ and $k\ge0$. On the complexification $\mathcal H^{\mathbb C}_{n,k}=\mathcal H_{n,k}\otimes_{\mathbb R}\mathbb C$, the action
--   $$(\rho_{n,k}(O)G)(x)=G(O^{-1}x),\qquad O\in SO(n),$$
--   is an irreducible unitary representation for the spherical $L^2$ inner product. Explicitly:
--   1. $\rho(O)$ maps $\mathcal H^{\mathbb C}_{n,k}$ into itself;
--   2. $\rho(I)G=G$ and $\rho(O_1O_2)G=\rho(O_1)\rho(O_2)G$;
--   3. $\int\rho(O)G\,\overline{\rho(O)H}\,d\sigma=\int G\,\overline H\,d\sigma$;
--   4. $\mathcal H^{\mathbb C}_{n,k}\neq\{0\}$;
--   5. its only $\rho$-invariant complex linear subspaces are $\{0\}$ and $\mathcal H^{\mathbb C}_{n,k}$.
--
--   This is the representation-theoretic input of the orbit-averaging identities (Fact 2.3) [Dai–Xu, Theorem 7.2].
--
--   **Formalization Note** $\mathcal H^{\mathbb C}_{n,k}$ is the space of complex homogeneous harmonic polynomials; $\rho(O)$ is a polynomial substitution.
--
--   Differences from the source:
--   - encoding: ℋ_{n,k} ⊗_ℝ ℂ → complex homogeneous harmonic polynomials of degree k; reason: the Laplacian has real coefficients, so p ⊗ c ↦ c·p is an isomorphism onto this space
--   - encoding: "is an irreducible unitary representation" → the clauses: ρ(O) preserves the space, ρ(I) = id, ρ(O₁O₂) = ρ(O₁)ρ(O₂), ρ(O) preserves ∫ G H̄ dσ, the space is nonzero, invariant subspaces are 0 or everything; reason: unfolding of the definition
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Theorem 2.2, p.12

import Mathlib
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_harmonicSpaceC
import Definitions.Def_PolySphereLP_rho
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Theorem 2.2 (Dai–Xu, [DX13, Theorem 7.2]).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Theorem 2.2, p.12.

Let `n ≥ 3`, `k ≥ 0`. On `ℋ^ℂ_{n,k} = ℋ_{n,k} ⊗_ℝ ℂ`, the action `(ρ(O)G)(x) = G(O⁻¹x)`,
`O ∈ SO(n)`, is an irreducible unitary representation for the spherical `L²` inner product; its only
invariant complex linear subspaces are `{0}` and `ℋ^ℂ_{n,k}`.

The conjuncts: `ρ(O)` maps `ℋ^ℂ_{n,k}` into itself; `ρ(I) = id` and `ρ(O₁O₂) = ρ(O₁)ρ(O₂)`
(a representation); `∫ ρ(O)G · conj(ρ(O)H) dσ = ∫ G · conj H dσ` (unitary); `ℋ^ℂ_{n,k} ≠ 0`; and every
`ρ`-invariant complex subspace `W ⊆ ℋ^ℂ_{n,k}` is `0` or `ℋ^ℂ_{n,k}` (irreducible).

**Formalization Note.** `ℋ^ℂ_{n,k}` is the space of complex homogeneous harmonic polynomials (see
`harmonicSpaceC`); `SO(n)` is `Matrix.specialOrthogonalGroup (Fin n) ℝ`. -/
theorem theorem_2_2_dai_xu_irreducibility (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    (∀ O ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, ∀ G ∈ harmonicSpaceC n k,
      rho O G ∈ harmonicSpaceC n k) ∧
    (∀ G ∈ harmonicSpaceC n k, rho 1 G = G) ∧
    (∀ O₁ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, ∀ O₂ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ,
      ∀ G ∈ harmonicSpaceC n k, rho (O₁ * O₂) G = rho O₁ (rho O₂ G)) ∧
    (∀ O ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, ∀ G ∈ harmonicSpaceC n k,
      ∀ H ∈ harmonicSpaceC n k,
        ∫ x, eval (fun i => (x i : ℂ)) (rho O G) * starRingEnd ℂ (eval (fun i => (x i : ℂ)) (rho O H))
            ∂(SphereSOS.Rate.sigma n) =
          ∫ x, eval (fun i => (x i : ℂ)) G * starRingEnd ℂ (eval (fun i => (x i : ℂ)) H)
            ∂(SphereSOS.Rate.sigma n)) ∧
    harmonicSpaceC n k ≠ ⊥ ∧
    (∀ W : Submodule ℂ (MvPolynomial (Fin n) ℂ), W ≤ harmonicSpaceC n k →
      (∀ O ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, ∀ G ∈ W, rho O G ∈ W) →
      W = ⊥ ∨ W = harmonicSpaceC n k) := by sorry

end PolySphereLP
