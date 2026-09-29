-- Prove2me | Theorems.Thm_ValuationSubring_exists_algEquiv_comap_eq_of_isGalois
-- name    : ValuationSubring.exists_algEquiv_comap_eq_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/f11c3ddc-f0c0-5b88-9caf-873a52a7dc75
-- title:
--   Galois transitivity on valuation rings over a DVR
-- statement:
--   Let $E$ and $K$ be fields with $K$ an $E$-algebra that is finite-dimensional over $E$ and Galois over $E$. Let $V$ be a valuation subring of $E$ whose underlying ring is a discrete valuation ring, and let $B$ and $B'$ be valuation subrings of $K$. Assume that each of $B$ and $B'$ lies over $V$ in the sense that for every $x \in E$ the image $\operatorname{algebraMap}_{E,K}(x)$ belongs to $B$ if and only if $x \in V$, and likewise for $B'$; that is, the contraction of each of $B$, $B'$ along the structure map $E \to K$ is exactly $V$. The conclusion is that there exists an $E$-algebra automorphism $\sigma$ of $K$ with $B' = B.\mathrm{comap}\,\sigma$, the preimage of $B$ under the ring homomorphism underlying $\sigma$; equivalently $B' = \sigma^{-1}(B)$, so that $\sigma$ carries $B'$ onto $B$. No minimality or normalisation of $V$ beyond its being a discrete valuation ring is assumed.
--
--   This is the conjugation theorem for valuation rings in a finite Galois extension: the Galois group acts transitively on the valuation subrings of $K$ contracting to a given one on $E$, here in the case of a discrete valuation ring on the base. It is used in the analysis of the branches of the special fibre of modular models, where the several valuation rings of a function field lying over a fixed discrete valuation must be compared up to Galois conjugacy.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algEquiv_comap_eq_of_isGalois.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_algEquiv_comap_eq_of_isGalois
    {E K : Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K] [IsGalois E K]
    (V : ValuationSubring E) [IsDiscreteValuationRing ↥V]
    (B B' : ValuationSubring K)
    (hB : ∀ x : E, algebraMap E K x ∈ B ↔ x ∈ V) (hB' : ∀ x : E, algebraMap E K x ∈ B' ↔ x ∈ V) :
    ∃ σ : K ≃ₐ[E] K, B' = B.comap σ.toAlgHom.toRingHom := by sorry
