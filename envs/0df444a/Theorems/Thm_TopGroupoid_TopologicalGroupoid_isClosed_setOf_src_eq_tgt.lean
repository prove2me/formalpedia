-- Prove2me | Theorems.Thm_TopGroupoid_TopologicalGroupoid_isClosed_setOf_src_eq_tgt
-- name    : TopGroupoid.TopologicalGroupoid.isClosed_setOf_src_eq_tgt
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:24.214392+00:00
-- url     : https://prove2.me/theorems/a51f1360-3e94-4d87-acc2-5bf741cf9dbf
-- title:
--   The inertia group $I=\{g\in\mathcal G: s(g)=t(g)\}$ of a topological groupoid is closed in $\mathcal G$ and, with the subspace topology, compactly generated weakly Hausdorff
-- statement:
--   **The inertia group of a topological groupoid is a closed subspace.** Let $(X,\mathcal G,s,t,c,e,i)$ be a topological groupoid, i.e. a groupoid internal to the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces: $X$ (objects) and $\mathcal G$ (arrows) are compactly generated weakly Hausdorff spaces and the source, target, unit, inversion and composition maps are continuous. Its *inertia group* (isotropy bundle) is
--   $$I_{[\mathcal G\rightrightarrows X]}=X\times_{\Delta,X\times X,(s,t)}\mathcal G\;\cong\;\{g\in\mathcal G:\ s(g)=t(g)\}=\bigcup_{x\in X}I_x ,$$
--   the set of arrows from an object to itself, a relative group over $X$ whose fibre over $x$ is the isotropy group $I_x=s^{-1}(x)\cap t^{-1}(x)$ (Definition E.6.3.4). Then:
--
--   1. $I=\{g\in\mathcal G: s(g)=t(g)\}$ is closed in $\mathcal G$;
--   2. $I$ with the subspace topology induced by $\mathcal G$ is compactly generated;
--   3. $I$ with the subspace topology is weakly Hausdorff.
--
--   Parts 2 and 3 say that the fibre product defining $I$ in $\mathbf{CGWH}$ carries the ordinary subspace topology, i.e. it "can be computed in $\mathbf{Spaces}$". The inertia group is the chart of the inertia stack of the quotient stack $[X/\mathcal G]$ (Lemma E.6.3.6) and interpolates the isotropy groups $I_x$ (Remark E.6.3.12).
--
--   **Formalization Note.** The topological groupoid is the platform structure `TopGroupoid.TopologicalGroupoid X R` (definition `TopGroupoid_TopologicalGroupoid`); $I$ is realized as the subset/subtype `{g : R // G.src g = G.tgt g}` of the arrow space, which is homeomorphic to the fibre product via the second projection. **Deviation from the source.** The paper asserts the computability in $\mathbf{Spaces}$ only under the extra hypothesis that $X$ is Hausdorff; parts 2-3 hold without it (a closed subspace of a compactly generated space is compactly generated, and subspaces of weakly Hausdorff spaces are weakly Hausdorff), so no Hausdorff hypothesis is imposed. Closedness of each single isotropy group $I_x$ and its group structure are the separate platform item `TopGroupoid.TopologicalGroupoid.isClosed_isotropy_and_exists_group`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 925, Lemma E.6.3.5 (with Definition E.6.3.4)

import Mathlib
import Definitions.Def_TopGroupoid_TopologicalGroupoid

open Topology

set_option autoImplicit false

universe u

namespace TopGroupoid

theorem TopologicalGroupoid.isClosed_setOf_src_eq_tgt {X R : Type u} [TopologicalSpace X]
    [TopologicalSpace R] (G : TopologicalGroupoid X R) :
    IsClosed {g : R | G.src g = G.tgt g} ∧
      CompactlyGeneratedSpace {g : R // G.src g = G.tgt g} ∧
      CGWH.WeaklyHausdorffSpace {g : R // G.src g = G.tgt g} := by sorry

end TopGroupoid
