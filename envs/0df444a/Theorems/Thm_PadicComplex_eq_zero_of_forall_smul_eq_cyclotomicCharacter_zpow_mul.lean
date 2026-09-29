-- Prove2me | Theorems.Thm_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul
-- name    : PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/a2e79c90-941b-5fd5-bfd0-7f508a589596
-- title:
--   Tate's vanishing: no nonzero χ^k-periods in ℂₚ
-- statement:
--   Let $p$ be a prime (carried as a `Fact` instance), let $k$ be a nonzero integer, and let $c$ be an element of $\mathbb{C}_p$, the completion `ℂ_[p]` of the algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$. Suppose that for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of `PadicAlgCl p` the scalar action of $\sigma$ on $c$ satisfies $\sigma \bullet c = \lambda(\sigma)^k\, c$, where $\lambda(\sigma) \in \mathbb{C}_p$ is obtained as follows: [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) sends $\sigma$ to the automorphism of `AlgebraicClosure ℚ` got by restricting $\sigma$ to a $\mathbb{Q}$-algebra map and then applying `AlgEquiv.restrictNormalHom` for the normal subextension `AlgebraicClosure ℚ` inside `PadicAlgCl p`; the $p$-adic cyclotomic character `cyclotomicCharacter (AlgebraicClosure ℚ) p` is evaluated at the underlying ring equivalence of this global automorphism, giving a unit of $\mathbb{Z}_p$, which is viewed in $\mathbb{Z}_p$, then in $\mathbb{Q}_p$, and finally mapped into $\mathbb{C}_p$ by the structure map; the $k$-th power is the integer power in the field $\mathbb{C}_p$. The conclusion is that $c = 0$.
--
--   This is Tate's vanishing theorem in the form $H^0(\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p), \mathbb{C}_p(k)) = 0$ for $k \neq 0$, with the twist given by the global cyclotomic character pulled back along the restriction of local automorphisms to $\overline{\mathbb{Q}}$. It is used for the variant phrased for fixing subgroups and, through that, in the construction of a basis of the $p$-adic Tate module of a $p$-divisible group on which the Galois action is by a power of the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul
    (p : ℕ) [Fact p.Prime] (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ • c =
        (algebraMap ℚ_[p] ℂ_[p]
            (((cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv :
                ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k * c) :
    c = 0 := by sorry
