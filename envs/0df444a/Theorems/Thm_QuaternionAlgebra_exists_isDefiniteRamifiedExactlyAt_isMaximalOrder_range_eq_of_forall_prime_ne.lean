-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne
-- name    : QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/bd350ca2-6022-5b3a-9a2d-36a15555caa7
-- title:
--   Rank-four ℤ-domains split away from p are maximal orders
-- statement:
--   Let $p$ be a prime and let $O$ be a ring with no zero divisors (and nontrivial), free and finite as a $\mathbb Z$-module with $\operatorname{rank}_{\mathbb Z} O = 4$; $O$ is not assumed commutative. Assume two hypotheses: first, for every prime $\ell \neq p$ there is a $\mathbb Z_\ell$-algebra isomorphism $\mathbb Z_\ell \otimes_{\mathbb Z} O \cong M_2(\mathbb Z_\ell)$; second, every $x \in O$ satisfying $x^2 - t\cdot x + n\cdot 1 = 0$ for some $t, n \in \mathbb Z$ with $p \mid t$ and $p^2 \mid n$ lies in $p\,O$, i.e. $x = p\,y$ for some $y \in O$. The conclusion asserts the existence of $a, b \in \mathbb Q$ such that, writing $B = \mathbb H[\mathbb Q, a, b]$ for the associated quaternion algebra: $a < 0$, $b < 0$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$ the algebra $B \otimes_{\mathbb Q} \mathbb Q_v$ has all nonzero elements invertible if and only if $p$ lies in the prime ideal of $v$; moreover there is a $\mathbb Z$-submodule $\Lambda \subseteq B$ which contains $1$, is closed under multiplication, has $\mathbb Q$-span all of $B$, is finitely generated, and is maximal among such submodules under inclusion, together with an injective ring homomorphism $\theta \colon O \to B$ whose image is exactly $\Lambda$.
--
--   This is the purely algebraic core of Deuring's description of endomorphism rings of supersingular elliptic curves: a $\mathbb Z$-order of rank four that is $M_2(\mathbb Z_\ell)$ away from $p$ and $p$-saturated in the stated sense is a maximal order in the definite rational quaternion algebra ramified exactly at $p$ (and at the archimedean place). It is used in the identification of the endomorphism ring of a supersingular Weierstrass curve, via [`WeierstrassCurve.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_rationalEndSubring`](thm.html#WeierstrassCurve.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_rationalEndSubring).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct

theorem QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne
    (p : ℕ) [Fact p.Prime] (O : Type*) [Ring O] [IsDomain O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hrank : Module.finrank ℤ O = 4)
    (hsplit : ∀ ℓ : ℕ, [Fact ℓ.Prime] → ℓ ≠ p →
      Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]))
    (hmaxp : ∀ x : O, (∃ t n : ℤ, x * x - t • x + n • (1 : O) = 0 ∧ (p : ℤ) ∣ t ∧ (p : ℤ) ^ 2 ∣ n) →
      ∃ y : O, x = (p : ℤ) • y) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p ∧
      ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsMaximalOrder Λ ∧
        ∃ θ : O →+* ℍ[ℚ, a, b], Function.Injective θ ∧ Set.range θ = (Λ : Set ℍ[ℚ, a, b]) := by sorry
