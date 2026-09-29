-- Prove2me | Theorems.Thm_RingHom_Finite_finite_localRingHom_of_forall_comap_eq
-- name    : RingHom.Finite.finite_localRingHom_of_forall_comap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/bb2d58c6-426b-556a-9f77-9d868340b478
-- title:
--   Finiteness of local rings at a unique prime above its contraction
-- statement:
--   Let $B$ and $C$ be commutative rings and let $\varphi\colon B \to C$ be a ring homomorphism which is finite, i.e. $C$ is a finitely generated $B$-module for the module structure induced by $\varphi$. Let $\mathfrak q \subset C$ be a prime ideal, and assume that $\mathfrak q$ is the only prime of $C$ contracting to $\varphi^{-1}(\mathfrak q)$: for every prime ideal $Q$ of $C$ with $\varphi^{-1}(Q) = \varphi^{-1}(\mathfrak q)$ one has $Q = \mathfrak q$. The conclusion is that the induced homomorphism of localisations $\mathrm{Localization.localRingHom}$ associated with the pair $(\varphi^{-1}(\mathfrak q), \mathfrak q)$ and $\varphi$ — that is, the local homomorphism $B_{\varphi^{-1}(\mathfrak q)} \to C_{\mathfrak q}$ extending $\varphi$, the equality $\varphi^{-1}(\mathfrak q) = \varphi^{-1}(\mathfrak q)$ being witnessed by reflexivity — is again finite: $C_{\mathfrak q}$ is a finitely generated module over $B_{\varphi^{-1}(\mathfrak q)}$.
--
--   This is the commutative-algebra statement that a finite ring map becomes module-finite on local rings whenever the chosen prime is alone in its fibre (the algebraic form of "finite and with a one-point fibre"). It is used to prove finiteness of the stalk map of a finite morphism of schemes at a point alone in its fibre, [`AlgebraicGeometry.IsFinite.finite_hom_stalkMap_of_forall_base_eq`](thm.html#AlgebraicGeometry.IsFinite.finite_hom_stalkMap_of_forall_base_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_Finite_finite_localRingHom_of_forall_comap_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.Finite.finite_localRingHom_of_forall_comap_eq
    {B C : Type*} [CommRing B] [CommRing C] (φ : B →+* C) (hφ : φ.Finite)
    (𝔮 : Ideal C) [𝔮.IsPrime]
    (huniq : ∀ Q : Ideal C, Q.IsPrime → Q.comap φ = 𝔮.comap φ → Q = 𝔮) :
    (Localization.localRingHom (𝔮.comap φ) 𝔮 φ rfl).Finite := by sorry
