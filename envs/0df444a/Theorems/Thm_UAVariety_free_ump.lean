-- Prove2me | Theorems.Thm_UAVariety_free_ump
-- name    : UAVariety.free_ump
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T14:18:26.474758+00:00
-- url     : https://prove2.me/theorems/6d270940-f629-4adb-9339-638269e3d3c4
-- title:
--   Universal mapping property of the free algebra
-- statement:
--   $L$ is a signature without relation symbols; an algebra is a type in `Type u` with an $L$-structure (`Alg L`), and $K$ is a class of algebras. $F_K(\bar X)=T(X)/\theta_K(X)$, where $T(X)$ is the term algebra over $X$ and $\theta_K(X)$ is the intersection of all congruences $\varphi$ on $T(X)$ with $T(X)/\varphi\in S(K)$; $\bar x$ and $\bar p$ are the classes of a variable and of a term. For every type $X$ in `Type u`, every $A\in K$ and every map $v:X\to A$ there is a unique homomorphism $f:F_K(\bar X)\to A$ with $f(\bar x)=v(x)$ for all $x\in X$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, Def 10.9 and Theorem 10.10 (Birkhoff)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- B&S Thm 10.10 (Birkhoff): `F_K(X̄)` has the universal mapping property for `K` over `X̄`:
every map of the generators into a member of `K` extends to a unique homomorphism. -/
theorem free_ump (K : Set (Alg L)) (X : Type u) (A : Alg L) (hA : A ∈ K) (v : X → A) :
    ∃! f : freeAlg K X →[L] A, ∀ x, f (freeGen K X x) = v x := by sorry

end UAVariety
