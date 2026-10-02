-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_midpoint_exchange_mem_base
-- name    : SteinitzExchange.Extension.midpoint_exchange_mem_base
-- status  : Proved
-- author  : @choi
-- created : 2026-10-01T03:34:19.912165+00:00
-- url     : https://prove2.me/theorems/3ac8d0ff-c3a8-4428-b097-3c19f40868c2
-- title:
--   Midpoint geometry yields a complementary pair of unit exchanges
-- statement:
--   Let $V$ be a finite nonempty coordinate set. Let $B,A\subseteq\mathbb Z^V$ be finite integral base sets: each is nonempty, and whenever $a,b$ lie in the set and $a_u>b_u$, there is a coordinate $v$ with $a_v<b_v$ such that $a-e_u+e_v$ also lies in the set. Here $e_u$ denotes the unit vector at $u$.
--
--   Suppose $x,y\in B$ have lattice distance four and their midpoint lies in the convex hull of $A$:
--   $$
--   \sum_{w\in V}|x_w-y_w|=4,\qquad \frac{x+y}{2}\in\operatorname{conv}(A).
--   $$
--   Then there are $u,v\in V$ satisfying
--   $$
--   x_u>y_u,\qquad x_v<y_v,\qquad x-e_u+e_v\in A,\qquad y+e_u-e_v\in A.
--   $$
--   This is the local geometric step that turns a midpoint condition into a simultaneous exchange. The two exchanged points may coincide, so the assertion also covers repeated exchange directions. The role of $B$ is to ensure that $x$ and $y$ have the same coordinate sum; no inclusion between $A$ and $B$ is required.
-- source:
--   Kazuo Murota, Convexity and Steinitz's Exchange Property, Advances in Mathematics 124 (1996), 272–311, DOI 10.1006/aima.1996.0084; https://scispace.com/pdf/convexity-and-steinitz-s-exchange-property-1h0w0a22vc.pdf; Section 4.2, proof of Theorem 4.4, midpoint c=(x+y)/2, box intersection after equation (4.8), and four-vertex matching argument, including the repeated-direction case. The statement isolates the unweighted integral-base geometry used in that proof.

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet

namespace SteinitzExchange.Extension


theorem midpoint_exchange_mem_base {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B A : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hx : x ∈ B) (hy : y ∈ B) (hxy : ∑ w, |x w - y w| = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
      x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A := by sorry

end SteinitzExchange.Extension
