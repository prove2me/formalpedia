-- Prove2me | Theorems.Thm_RingHom_Etale_isPushout_frobenius
-- name    : RingHom.Etale.isPushout_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/b63a49f3-029d-5366-918d-f024da01d513
-- title:
--   The Frobenius square of an étale ring map is a pushout
-- statement:
--   Let $A$ and $B$ be commutative rings in a fixed universe, let $p$ be a prime, and suppose both $A$ and $B$ have characteristic $p$. Let $\varphi : A \to B$ be a ring homomorphism satisfying `RingHom.Etale`, i.e. $\varphi$ is étale. The assertion is that the square in the category `CommRingCat` whose two maps out of $A$ are the absolute Frobenius endomorphism $\mathrm{frobenius}\ A\ p : a \mapsto a^p$ of $A$ and the map $\varphi$, and whose two maps into $B$ are $\varphi$ and the absolute Frobenius endomorphism $\mathrm{frobenius}\ B\ p : b \mapsto b^p$ of $B$, is a pushout square: it commutes (the outer square $\varphi \circ \mathrm{frobenius}_A = \mathrm{frobenius}_B \circ \varphi$, which holds since $\varphi$ is a ring map) and the resulting cocone on $\mathrm{frobenius}_A$ along $\varphi$ is universal. Equivalently, $B$ together with $\varphi$ and $\mathrm{frobenius}_B$ realises the tensor product $A \otimes_{A,\mathrm{frobenius}_A} B$, i.e. the relative Frobenius $B^{(p)} \to B$ of the étale $A$-algebra $B$ is an isomorphism.
--
--   This is the ring-theoretic form of the statement that the relative Frobenius of an étale morphism of $\mathbf{F}_p$-schemes is an isomorphism, so that the absolute Frobenius of an étale $A$-algebra is a base change of the absolute Frobenius of $A$. It is used in [`AlgebraicGeometry.SmoothOfRelativeDimension.finrank_eq_pow_of_isPullback_frobenius`](thm.html#AlgebraicGeometry.SmoothOfRelativeDimension.finrank_eq_pow_of_isPullback_frobenius), where étale-local comparison with affine space computes the rank of Frobenius on a smooth scheme as a power of $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_Etale_isPushout_frobenius.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

theorem RingHom.Etale.isPushout_frobenius
    {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]
    {φ : A →+* B} (hφ : φ.Etale) :
    IsPushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (frobenius B p)) := by sorry
