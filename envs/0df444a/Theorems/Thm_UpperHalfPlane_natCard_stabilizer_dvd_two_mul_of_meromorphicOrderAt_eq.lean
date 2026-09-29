-- Prove2me | Theorems.Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
-- name    : UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/a5e20f5a-1f5d-5472-a477-cd7fdc9911b8
-- title:
--   Stabiliser order divides twice the meromorphic order at τ
-- statement:
--   Let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbb Z)$ and let $F \colon \mathfrak H \to \mathbb C$ be a function on the upper half-plane which is $\Gamma$-invariant in the strong sense that $F(\gamma \cdot \tau) = F(\tau)$ for every $\gamma \in \Gamma$ and every $\tau \in \mathfrak H$. Fix a point $\tau \in \mathfrak H$ and an integer $n$, and transport $F$ to a function of a complex variable by composing with `UpperHalfPlane.ofComplex`, the map $\mathbb C \to \mathfrak H$ which is the identity on points of positive imaginary part. Assume that the meromorphic order at $\tau$ of $z \mapsto F(\mathrm{ofComplex}\, z)$ equals $n$; since $n$ is an integer rather than $\top$, this in particular excludes the case of a function vanishing identically near $\tau$. The conclusion is a divisibility in $\mathbb Z$: the cardinality $\#\mathrm{Stab}_\Gamma(\tau)$, computed as a natural number and cast to $\mathbb Z$, divides $2n$. No assumption is made that $-1 \in \Gamma$, that $\Gamma$ has finite index, or that the stabiliser is finite.
--
--   This is the classical statement that the order of vanishing or of the pole of a $\Gamma$-invariant meromorphic function at an elliptic point $\tau$ is divisible by the elliptic order $e_\tau = \#\mathrm{Stab}_\Gamma(\tau)/2$ (twice the order appearing because $\pm 1$ act trivially). It is used in the project to compute ramification of the quotient map to a modular curve, being cited for instance by [`ModularCurve.ComplexPlaceDictionaryOf.card_stabilizer_dvd_two_mul_ramification`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.card_stabilizer_dvd_two_mul_ramification), by [`ModularCurve.ComplexPlaceDictionary.two_mul_ramification_eq_card_stabilizer`](thm.html#ModularCurve.ComplexPlaceDictionary.two_mul_ramification_eq_card_stabilizer) and in the study of Abel–Jacobi fibre sums modulo period lattices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
    (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (τ : ℍ) (n : ℤ)
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by sorry
