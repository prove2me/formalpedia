-- Prove2me | Theorems.Thm_PadicInt_exists_finiteFlat_kummerHopf_withConv_aeval
-- name    : PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/dc3c7b7a-26cf-533b-999a-ca618517b3cb
-- title:
--   Kummer Hopf algebra over ℤₚ with polynomial point evaluations
-- statement:
--   Let $p$ be a prime, let $u \in \mathbb{Q}_p$ have $\|u\|_+ = 1$ (norm one as a non-negative real), and let $\zeta, \eta$ lie in an algebraic closure of $\mathbb{Q}_p$ with $\zeta$ a primitive $p$-th root of unity and $\eta^p$ equal to the image of $u$ under the structure map $\mathbb{Q}_p \to \overline{\mathbb{Q}_p}$. The assertion is the existence of a type $H$ carrying a commutative ring structure and a Hopf algebra structure over $\mathbb{Z}_p$ such that: $H$ is finite as a $\mathbb{Z}_p$-module, $H$ is flat as a $\mathbb{Z}_p$-module, its comultiplication is cocommutative, and there is a bijection $\psi$ from $\mathbb{Z}/p \times \mathbb{Z}/p$ onto the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to \overline{\mathbb{Q}_p}$, regarded as a monoid under convolution (`WithConv`), which is additive-to-multiplicative: $\psi(a+b) = \psi(a)\,\psi(b)$ for all $a, b$. Moreover there is a family of polynomials $F : H \to \mathbb{Z}/p \to \mathbb{Z}_p[X]$ with $\psi(i,j)(h) = \mathrm{aeval}\bigl(\zeta^{\,i.\mathrm{val}} \eta^{\,j.\mathrm{val}}\bigr)\,\bigl(F(h)(j)\bigr)$ for all $i, j \in \mathbb{Z}/p$ and all $h \in H$, the exponents being the representatives in $\{0,\dots,p-1\}$. No Galois-equivariance clause is asserted; $F$ is required to be neither linear nor canonical.
--
--   This realises the Oort–Tate type Kummer group scheme attached to a $p$-adic unit $u$ as a finite flat cocommutative Hopf algebra over $\mathbb{Z}_p$ whose $\overline{\mathbb{Q}_p}$-points form a group isomorphic to $(\mathbb{Z}/p)^2$, with each point given by evaluating a $\mathbb{Z}_p$-polynomial at the monomial $\zeta^i \eta^j$. The explicit evaluation description is what makes Galois equivariance a formal consequence, and it is used in [`PadicInt.exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one`](thm.html#PadicInt.exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_finiteFlat_kummerHopf_withConv_aeval.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal

theorem PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval
    (p : ℕ) [Fact p.Prime] (u : ℚ_[p]) (hu : ‖u‖₊ = 1)
    (ζ η : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ p)
    (hη : η ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) u) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ ψ : (ZMod p × ZMod p) ≃ WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
        ∃ F : H → ZMod p → Polynomial ℤ_[p],
          ∀ (i j : ZMod p) (h : H),
            (ψ (i, j)) h
              = Polynomial.aeval (ζ ^ i.val * η ^ j.val) (F h j) := by sorry
