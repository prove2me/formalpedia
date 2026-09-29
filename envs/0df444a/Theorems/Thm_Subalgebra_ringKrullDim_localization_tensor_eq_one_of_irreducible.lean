-- Prove2me | Theorems.Thm_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible
-- name    : Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/3fe27020-f276-57c2-80d8-3e23c2fc0407
-- title:
--   Krull dimension one for fibres of normal subalgebras over Λ[X]
-- statement:
--   Let $\Lambda$ be a principal ideal domain, $p \in \Lambda$ an irreducible element, and $K$ a field equipped with a $\Lambda$-algebra structure (with $\Lambda$ and $K$ in the same universe). Let $R$ and $A$ be $\Lambda$-subalgebras of $K$, suppose given a $\Lambda$-algebra isomorphism $e : \Lambda[X] \simeq R$ from the polynomial ring in one variable, and suppose $R \le A$, that every element of $A$ is integral over $R$ when viewed in $K$, that $A$ is of finite type as a $\Lambda$-algebra, and that $A$ is integrally closed (in its fraction field). Let $k$ be a field, in a possibly different universe, with a $\Lambda$-algebra structure such that the image of $p$ in $k$ is zero, and let $\mathfrak{m}$ be a maximal ideal of the tensor product $k \otimes_\Lambda A$. Then the ring Krull dimension of the localisation of $k \otimes_\Lambda A$ at $\mathfrak{m}$ equals $1$ (as an element of the extended integers $\mathbb{Z} \cup \{\pm\infty\}$).
--
--   This is the concrete form, for a pair of subalgebras of a field, of the assertion that the fibre over a closed point of $\operatorname{Spec} \Lambda$ of a normal domain finite over $\Lambda[X]$ is equidimensional of dimension one. It is applied to the chart rings of the normalisation of the affine $j$-line in a modular function field, and is cited in the verification that the fibres of the resulting models of modular curves are regular at the relevant points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct Polynomial

universe u v

theorem Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible
    {Λ K : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [Field K] [Algebra Λ K] (R A : Subalgebra Λ K) (e : Λ[X] ≃ₐ[Λ] R) (hRA : R ≤ A)
    (hint : ∀ a : A, IsIntegral R (a : K))
    (hFT : Algebra.FiniteType Λ A) (hIC : IsIntegrallyClosed A)
    (k : Type v) [Field k] [Algebra Λ k] (hk : algebraMap Λ k p = 0)
    (m : Ideal (k ⊗[Λ] A)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by sorry
