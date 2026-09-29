-- Prove2me | Theorems.Thm_RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X
-- name    : RingEquiv.false_of_apply_eq_X_pow_of_apply_eq_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/a305b304-9362-52ee-ac80-c54e09653fab
-- title:
--   No ring can carry a swapped X/Xᵖ pair of isomorphisms to k[X]
-- statement:
--   Let $p$ be a natural number with $2 \le p$, let $k$ be a nontrivial commutative ring, and let $R$ be a commutative ring. Suppose given two ring isomorphisms $e_0, e_1 \colon R \xrightarrow{\sim} k[X]$ (isomorphisms of additive and multiplicative structure, i.e. `R ≃+* Polynomial k`) and two elements $a, b \in R$ such that $e_0(a) = X$ and $e_0(b) = X^p$, while $e_1(b) = X$ and $e_1(a) = X^p$; thus the two isomorphisms interchange the roles of the pair $(a,b)$, each sending one of the elements to the indeterminate $X$ and the other to its $p$-th power. The conclusion is `False`: no such data exist. Equivalently, a single commutative ring cannot admit two identifications with the polynomial ring $k[X]$ over a nontrivial base under which a fixed pair of its elements corresponds to $(X, X^p)$ in one identification and to $(X^p, X)$ in the other, once $p \ge 2$.
--
--   An elementary degree obstruction in $k[X]$, with no classical name. It is used in the construction of the Deligne–Rapoport-style model of the modular curve of level $p$, where it separates the two minimal primes above $p$ of an affine chart ring: their residue rings are polynomial rings in $\bar\jmath$ and in $\bar\jmath_p$ respectively, with the other coordinate becoming a $p$-th power, so the primes cannot coincide. It is cited by [`ModularCurve.DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial`](thm.html#ModularCurve.DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem RingEquiv.false_of_apply_eq_X_pow_of_apply_eq_X
    (p : ℕ) (hp : 2 ≤ p) (k : Type v) [CommRing k] [Nontrivial k]
    (R : Type u) [CommRing R] (e₀ e₁ : R ≃+* Polynomial k) (a b : R)
    (h₀a : e₀ a = Polynomial.X) (h₀b : e₀ b = Polynomial.X ^ p)
    (h₁b : e₁ b = Polynomial.X) (h₁a : e₁ a = Polynomial.X ^ p) : False := by sorry
