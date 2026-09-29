-- Prove2me | Theorems.Thm_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd
-- name    : Rat.exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/32642570-53bc-5a98-82cc-a75c7311f0b7
-- title:
--   Squares modulo odd p are squares in ℚᵥ
-- statement:
--   Let $p$ be a natural number that is prime and different from $2$, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ of the number field $\mathbb{Q}$, and suppose the image of $p$ in $\mathcal{O}_{\mathbb{Q}}$ lies in the prime ideal $v.\mathrm{asIdeal}$, so that $v$ is the place of $\mathbb{Q}$ above $p$. Let $u$ be an integer that is not divisible by $p$ and whose reduction in $\mathbb{Z}/p\mathbb{Z}$ is a square, i.e. equals $t\cdot t$ for some element $t$ of $\mathbb{Z}/p\mathbb{Z}$. The assertion is that there exists an element $s$ of the $v$-adic completion $v.\mathrm{adicCompletion}\ \mathbb{Q}$ with $s^2$ equal to the image of the rational number $u$ under the structure map $\mathbb{Q} \to v.\mathrm{adicCompletion}\ \mathbb{Q}$. In other words, an odd-$p$ unit that is a quadratic residue modulo $p$ becomes a square in the completion of $\mathbb{Q}$ at the place above $p$.
--
--   This is the standard lifting criterion for squares in $\mathbb{Q}_p$ at odd $p$ (Hensel's lemma for $X^2-u$), stated for the completion at the height-one prime of $\mathcal{O}_{\mathbb{Q}}$ above $p$ rather than for $\mathbb{Q}_p$ itself. It feeds the local computations of Hilbert symbols used to decide isotropy of ternary quadratic forms, and hence the existence of quaternion algebras over $\mathbb{Q}$ ramified at a prescribed set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Rat.exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (hsq : IsSquare (u : ZMod p)) :
    ∃ s : v.adicCompletion ℚ, s ^ 2 = algebraMap ℚ (v.adicCompletion ℚ) (u : ℚ) := by sorry
