-- Prove2me | Theorems.Thm_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
-- name    : PadicInt.exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/99e6e93d-e628-5882-adb5-cc73942ecc9b
-- title:
--   Kummer Hopf algebra witness with upper-triangular Galois action
-- statement:
--   Let $p$ be a prime and let $u \in \mathbb{Q}_p$ satisfy $\lVert u \rVert = 1$, i.e. $u$ is a $p$-adic unit. Let $\zeta, \eta$ be elements of $\overline{\mathbb{Q}_p} =$ `AlgebraicClosure ℚ_[p]` with $\zeta$ a primitive $p$-th root of unity and $\eta^p$ equal to the image of $u$ under the structure map $\mathbb{Q}_p \to \overline{\mathbb{Q}_p}$. Then there exists a type $H$ carrying a commutative ring structure and a Hopf algebra structure over $\mathbb{Z}_p$ such that $H$ is finite as a $\mathbb{Z}_p$-module, flat as a $\mathbb{Z}_p$-module, and cocommutative as a $\mathbb{Z}_p$-coalgebra, together with a bijection $\psi$ from $\mathbb{Z}/p \times \mathbb{Z}/p$ onto the set $\mathrm{Hom}_{\mathbb{Z}_p\text{-alg}}(H, \overline{\mathbb{Q}_p})$ equipped with its convolution multiplication (`WithConv`), subject to two conditions: first, $\psi(a+b) = \psi(a) \cdot \psi(b)$ for all $a, b \in \mathbb{Z}/p \times \mathbb{Z}/p$, the product being convolution, so that $\psi$ carries the additive group onto the points of $H$; second, for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$ and all natural numbers $e, c$ with $\sigma\zeta = \zeta^e$ and $\sigma\eta = \zeta^c \eta$, one has $\psi(e \cdot i + c \cdot j,\, j)(h) = \sigma\bigl(\psi(i,j)(h)\bigr)$ for all $i, j \in \mathbb{Z}/p$ and all $h \in H$.
--
--   This is the Hopf-algebra form of the Oort–Tate style witness for the Kummer extension of $\mathbb{Z}/p$ by $\mu_p$ attached to a unit class $[u] \in \mathbb{Z}_p^\times/(\mathbb{Z}_p^\times)^p$: a finite flat cocommutative Hopf algebra over $\mathbb{Z}_p$ whose $\overline{\mathbb{Q}_p}$-points form a group isomorphic to $\mathbb{Z}/p \times \mathbb{Z}/p$ on which the Galois action is upper triangular with diagonal entries the cyclotomic character and $1$. It is used in the construction of finite flat prolongations of the $p$-torsion of a Tate curve over $\mathbb{Z}_p$, in the cases $p = 2$, $p = 3$ and $p \ge 5$ separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal

theorem PadicInt.exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
    (p : ℕ) [Fact p.Prime] (u : ℚ_[p]) (hu : ‖u‖₊ = 1)
    (ζ η : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ p)
    (hη : η ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) u) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ ψ : (ZMod p × ZMod p) ≃ WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
          σ ζ = ζ ^ e → σ η = ζ ^ c * η →
          ∀ (i j : ZMod p) (h : H),
            (ψ (e • i + c • j, j)) h = σ ((ψ (i, j)) h) := by sorry
