-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_proto_basic_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P06.proto_basic_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:33:25.190894+00:00
-- url     : https://prove2.me/theorems/e65b1393-a1db-45e9-b4ca-f178e3a714ec
-- title:
--   Theorem 2.1
-- statement:
--   Let $F$ be a unital complex algebra, $X$ a complex Banach space, and $\Phi:F\to\mathcal C(X)$ a proto-calculus. All operator equations below include equality of domains. For $f,g\in F$ and $\lambda\in\mathbb C$:
--
--   1. If $\lambda\ne0$ or $\Phi(f)$ is everywhere bounded, then $\Phi(\lambda f)=\lambda\Phi(f)$.
--   2. If $\Phi(g)$ is everywhere bounded, then $\Phi(f)+\Phi(g)=\Phi(f+g)$ and $\Phi(f)\Phi(g)=\Phi(fg)$.
--   3. If $fg=1$, then $\Phi(g)$ is injective and $\Phi(g)^{-1}\subseteq\Phi(f)$; if also $fg=gf$, the inclusion is equality.
--   4. The bounded part is a unital complex subalgebra, and its restriction is a unital algebra representation by bounded operators.
--
--   $$\operatorname{bdd}(F,\Phi)=\{f\in F:\Phi(f)\in\mathcal L(X)\}.$$
--
--   These statements retain the noncommutative setting and the exceptional zero scalar.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 5, Theorem 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Theorem 2.1, PDF p.5: all four assertions, with actual domains and a
noncommutative ambient algebra. The zero-scalar exception is explicit. -/
theorem proto_basic_properties [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi) :
    (∀ (c : ℂ) f, c ≠ 0 ∨ Bounded (Phi f) → Phi (c • f) = graphScale c (Phi f)) ∧
    (∀ f g, Bounded (Phi g) →
      graphAdd (Phi f) (Phi g) = Phi (f + g) ∧ graphMul (Phi f) (Phi g) = Phi (f * g)) ∧
    (∀ f g, f * g = 1 → InjectiveGraph (Phi g) ∧ graphInverse (Phi g) ⊆ Phi f ∧
      (f * g = g * f → graphInverse (Phi g) = Phi f)) ∧
    (∃ B : Subalgebra ℂ F, (B : Set F) = boundedElements Phi ∧
      ∃ rho : B →ₐ[ℂ] (X →L[ℂ] X), ∀ f : B, Phi (f : F) = banachBoundedGraph (rho f)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
