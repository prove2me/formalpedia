-- Prove2me | Theorems.Thm_Rep_shortExact_map_tensorLeft_of_splitting
-- name    : Rep.shortExact_map_tensorLeft_of_splitting
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/ebbbcb5d-a8d8-5c07-b259-159437f93d80
-- title:
--   Left tensoring preserves k-linearly split short exact sequences
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in a single universe $u$), and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category `Rep k G` of $k$-linear representations of $G$. Assume $X$ is short exact, i.e. $f$ is a monomorphism, $g$ is an epimorphism and the complex is exact at the middle term. Assume further that $g$ admits a $k$-linear (not necessarily $G$-equivariant) section: a $k$-linear map $s \colon X_3 \to X_2$ between the underlying modules with $g(s(x)) = x$ for all $x \in X_3$. Then for every representation $A$ in `Rep k G`, the image of $X$ under the functor $A \otimes -$ on `Rep k G`, namely the short complex $A \otimes_k X_1 \to A \otimes_k X_2 \to A \otimes_k X_3$ with the maps $\mathrm{id}_A \otimes f$ and $\mathrm{id}_A \otimes g$ and the diagonal $G$-action, is again short exact.
--
--   This is the standard statement that tensoring a $k$-split short exact sequence of $G$-representations with a fixed representation on the left preserves short exactness; the $k$-linear splitting is what makes the left-hand map stay injective for an arbitrary coefficient ring $k$. It is used in the construction of cup products on Tate cohomology and their formal properties (associativity, commutativity, evaluation against the character dual), where short exact sequences are tensored in the second variable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_map_tensorLeft_of_splitting.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

theorem Rep.shortExact_map_tensorLeft_of_splitting {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (A : Rep.{u} k G) :
    (X.map (MonoidalCategory.tensorLeft A)).ShortExact := by sorry
