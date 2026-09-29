-- Prove2me | Theorems.Thm_RingHom_exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow
-- name    : RingHom.exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/56f280fd-6fa1-5412-80e5-217e0f2f2343
-- title:
--   Adic completions along a surjection with 𝔭-adically null kernel
-- statement:
--   Let $B$ and $C$ be commutative rings (in a common universe), let $\theta : B \to C$ be a ring homomorphism which is surjective as a function, and let $\mathfrak m$ be an ideal of $C$. Write $\mathfrak p = \theta^{-1}(\mathfrak m) =$ `Ideal.comap θ 𝔪`. Assume that for every natural number $n$ the kernel of $\theta$ is contained in $\mathfrak p^{n}$. Then there exists a ring isomorphism $e$ from the $\mathfrak p$-adic completion of $B$ onto the $\mathfrak m$-adic completion of $C$ (Mathlib's `AdicCompletion`, realised as the inverse limit of the quotients $B/\mathfrak p^{n}$, resp. $C/\mathfrak m^{n}$) such that for every $b \in B$ one has $e(\iota_B(b)) = \iota_C(\theta(b))$, where $\iota_B$ and $\iota_C$ denote the canonical structure maps $B \to \widehat{B}_{\mathfrak p}$ and $C \to \widehat{C}_{\mathfrak m}$ given by `algebraMap`. The assertion is existential: an isomorphism compatible with $\theta$ on the images of $B$ and $C$ is produced, with no further uniqueness or functoriality claim.
--
--   This is the standard comparison statement that an adic completion only depends on the quotient by an ideal that is adically negligible: a surjection whose kernel lies in all powers of the preimage ideal induces an isomorphism of completions. It is used in the analysis of completed local rings of modular curves, where local rings at cusps or at points in the relevant moduli problems are compared with explicit power-series-type rings via surjections with adically null kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u

theorem RingHom.exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow
    {B C : Type u} [CommRing B] [CommRing C] (θ : B →+* C) (hθ : Function.Surjective θ)
    (𝔪 : Ideal C) (hker : ∀ n : ℕ, RingHom.ker θ ≤ (Ideal.comap θ 𝔪) ^ n) :
    ∃ e : AdicCompletion (Ideal.comap θ 𝔪) B ≃+* AdicCompletion 𝔪 C,
      ∀ b : B, e (algebraMap B (AdicCompletion (Ideal.comap θ 𝔪) B) b) = algebraMap C (AdicCompletion 𝔪 C) (θ b) := by sorry
