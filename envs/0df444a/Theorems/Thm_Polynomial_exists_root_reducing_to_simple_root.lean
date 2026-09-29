-- Prove2me | Theorems.Thm_Polynomial_exists_root_reducing_to_simple_root
-- name    : Polynomial.exists_root_reducing_to_simple_root
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/1170401a-6191-5d2f-a9e6-f1bbe02a8b15
-- title:
--   Simple roots lift under reduction of a split polynomial
-- statement:
--   Let $A$ and $k$ be commutative rings that are integral domains, let $\mathrm{red} : A \to k$ be a ring homomorphism, let $s$ be a multiset of elements of $A$, and set $Q = \prod_{a \in s} (X - C(a)) \in A[X]$, the product over $s$ (with multiplicity) of the linear factors $X - C(a)$. Let $b \in k$ and assume that the root multiplicity of $b$ in the image polynomial $\mathrm{red}_*(Q) \in k[X]$, obtained by applying $\mathrm{red}$ to the coefficients, equals $1$. Then there exists $a$ belonging to $s$ such that $\mathrm{red}(a) = b$, the root multiplicity of $a$ in $Q$ equals $1$, and every $a'$ in $s$ with $\mathrm{red}(a') = b$ equals $a$. Thus a simple root of the reduction of a split monic polynomial is the image of exactly one element of the root multiset $s$, and that element is in turn a simple root of $Q$.
--
--   An elementary statement about reduction of a polynomial that splits with prescribed root multiset: simple roots downstairs are hit by a unique, and simple, root upstairs. It is used in the analysis of fibres and of place specialisations for models of modular curves in characteristic $p$, where a simple root of a reduced equation must be tracked back to a unique root of the original equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_root_reducing_to_simple_root.lean

import Mathlib.Algebra.Polynomial.Roots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Polynomial.exists_root_reducing_to_simple_root {A k : Type*} [CommRing A] [IsDomain A] [CommRing k] [IsDomain k] (red : A →+* k) (s : Multiset A) (b : k) (hb : ((s.map fun a => Polynomial.X - Polynomial.C a).prod.map red).rootMultiplicity b = 1) : ∃ a ∈ s, red a = b ∧ (s.map fun a => Polynomial.X - Polynomial.C a).prod.rootMultiplicity a = 1 ∧ ∀ a' ∈ s, red a' = b → a' = a := by sorry
