-- Prove2me | Theorems.Thm_PadicInt_ringHom_eq_ringHom_of_isNilpotent
-- name    : PadicInt.ringHom_eq_ringHom_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/a3a07e34-2e69-5baa-8938-ed7a542cc783
-- title:
--   Uniqueness of ring maps ℤₚ → B when p is nilpotent
-- statement:
--   Let $p$ be a prime natural number and let $B$ be a commutative ring (in a fixed universe) in which the image of $p$ under the canonical map $\mathbb{N} \to B$ is nilpotent, i.e. $(p : B)^n = 0$ for some $n$. Then any two ring homomorphisms $f, g \colon \mathbb{Z}_p \to B$ from the $p$-adic integers to $B$ are equal as ring homomorphisms. Equivalently: the ring $\mathbb{Z}_p$ admits at most one $B$-valued point whenever $p$ is nilpotent in $B$, so that a $\mathbb{Z}_p$-algebra structure on such a $B$ is unique once it exists. No finiteness, Noetherian or local hypothesis is imposed on $B$, and no compatibility with the topology of $\mathbb{Z}_p$ is assumed; the conclusion is the unconditional equality of the two homomorphisms.
--
--   This is the statement that $\operatorname{Spec} \mathbb{Z}_p$ is a limit of the $\mathbb{Z}/p^n$, so that $\mathbb{Z}_p$-algebra structures on rings killed by a power of $p$ are unique; it is used to identify the $\mathbb{Z}_p$-structures appearing in the Čerednik–Drinfel'd formal moduli package, in particular in the comparison of period maps and of the associated formal schemes with $\Omega$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_ringHom_eq_ringHom_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem PadicInt.ringHom_eq_ringHom_of_isNilpotent (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (hB : IsNilpotent (p : B)) (f g : ℤ_[p] →+* B) : f = g := by sorry
