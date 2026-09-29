-- Prove2me | Theorems.Thm_PadicInt_exists_etale_algebra_algHom_equiv_zmod
-- name    : PadicInt.exists_etale_algebra_algHom_equiv_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/455af69b-fd48-5dd0-aad6-66221c39cb75
-- title:
--   Unramified degree-n étale ℤₚ-algebra with ℤ/n-torsor of points
-- statement:
--   Let $p$ be a prime and let $n$ be a natural number with $n > 0$. The assertion is the existence of a type $B$ carrying a commutative ring structure and a $\mathbb{Z}_p$-algebra structure such that: $B$ is finite as a $\mathbb{Z}_p$-module, free as a $\mathbb{Z}_p$-module, and étale as a $\mathbb{Z}_p$-algebra; and, writing $G = \mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ for the group of $\mathbb{Q}_p$-algebra automorphisms of the algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$, there are a group homomorphism $\chi \colon G \to \mathbb{Z}/n$ (with $\mathbb{Z}/n$ written multiplicatively) and a bijection $x$ from $\mathbb{Z}/n$ to the set of $\mathbb{Z}_p$-algebra homomorphisms $B \to \overline{\mathbb{Q}}_p$ such that $\chi$ is surjective and, for every $\sigma \in G$ and every $i \in \mathbb{Z}/n$, one has $x(\chi(\sigma) + i) = \sigma \circ x(i)$, where $\sigma$ is regarded as a $\mathbb{Z}_p$-algebra homomorphism $\overline{\mathbb{Q}}_p \to \overline{\mathbb{Q}}_p$ by restriction of scalars. Thus $\mathrm{Hom}_{\mathbb{Z}_p}(B, \overline{\mathbb{Q}}_p)$ has exactly $n$ elements and is a $\mathbb{Z}/n$-torsor on which $G$ acts through the surjection $\chi$. No continuity or unramifiedness statement about $\chi$ is asserted separately.
--
--   This packages the unramified extension of $\mathbb{Q}_p$ of degree $n$, namely $\mathbb{Q}_p(\mu_{p^n-1})$ with its ring of integers, in the form of a finite free étale $\mathbb{Z}_p$-algebra whose $\overline{\mathbb{Q}}_p$-points are permuted simply transitively by $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ acting through a surjective character onto $\mathbb{Z}/n$. It is used in the construction of locally flat cocycles for residual Galois representations, in [`ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one`](thm.html#ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_etale_algebra_algHom_equiv_zmod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PadicInt.exists_etale_algebra_algHom_equiv_zmod
    (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra ℤ_[p] B),
      Module.Finite ℤ_[p] B ∧ Module.Free ℤ_[p] B ∧ Algebra.Etale ℤ_[p] B ∧
      ∃ (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Multiplicative (ZMod n))
        (x : ZMod n ≃ (B →ₐ[ℤ_[p]] PadicAlgCl p)),
        Function.Surjective χ ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (i : ZMod n),
          x (Multiplicative.toAdd (χ σ) + i) =
            ((σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).restrictScalars ℤ_[p]).comp (x i) := by sorry
